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
open import encode


module type_sys_props_term {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--TERMneqNAT : {z : Term} → ¬ TERM z ≡ NAT
--TERMneqNAT {z} ()

TERMneqQNAT : {z : Term} → ¬ TERM z ≡ QNAT
TERMneqQNAT {z} ()

--TERMneqTNAT : {z : Term} → ¬ TERM z ≡ TNAT
--TERMneqTNAT {z} ()

TERMneqPURE : {z : Term} → ¬ TERM z ≡ PURE
TERMneqPURE {z} ()

TERMneqNOSEQ : {z : Term} → ¬ TERM z ≡ NOSEQ
TERMneqNOSEQ {z} ()

TERMneqNOENC : {z : Term} → ¬ TERM z ≡ NOENC
TERMneqNOENC {z} ()

TERMneqLT : {c d : Term} {z : Term} → ¬ TERM z ≡ LT c d
TERMneqLT {c} {d} {z} ()

TERMneqQLT : {c d : Term} {z : Term} → ¬ TERM z ≡ QLT c d
TERMneqQLT {c} {d} {z} ()

TERMneqFREE : {z : Term} → ¬ TERM z ≡ FREE
TERMneqFREE {z} ()

TERMneqPI : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ PI c d
TERMneqPI {c} {d} {z} ()

TERMneqW : {c d e : Term} {z : Term} → ¬ TERM z ≡ WT c d e
TERMneqW {c} {d} {e} {z} ()

TERMneqM : {c d e : Term} {z : Term} → ¬ TERM z ≡ MT c d e
TERMneqM {c} {d} {e} {z} ()

TERMneqSUM : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ SUM c d
TERMneqSUM {c} {d} {z} ()

TERMneqSET : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ SET c d
TERMneqSET {c} {d} {z} ()

TERMneqISECT : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ ISECT c d
TERMneqISECT {c} {d} {z} ()

TERMneqTUNION : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ TUNION c d
TERMneqTUNION {c} {d} {z} ()

TERMneqUNION : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ UNION c d
TERMneqUNION {c} {d} {z} ()

--TERMneqQTUNION : {c : Term} {d : Term} {z : Term} → ¬ TERM z ≡ QTUNION c d
--TERMneqQTUNION {c} {d} {z} ()

TERMneqEQ : {c d e : Term} {z : Term} → ¬ TERM z ≡ EQ c d e
TERMneqEQ {c} {d} {e} {z} ()

TERMneqPARTIAL : {c : Term} {z : Term} → ¬ TERM z ≡ PARTIAL c
TERMneqPARTIAL {c} {z} ()

TERMneqFFDEFS : {c d : Term} {z : Term} → ¬ TERM z ≡ FFDEFS c d
TERMneqFFDEFS {c} {d} {z} ()

TERMneqSUBSING : {b : Term} {z : Term} → ¬ TERM z ≡ SUBSING b
TERMneqSUBSING {b} {z} ()

--TERMneqLIFT : {c : Term} {z : Term} → ¬ TERM z ≡ LIFT c
--TERMneqLIFT {c} {z} ()

--TERMneqTSQUASH : {c : Term} {z : Term} → ¬ TERM z ≡ TSQUASH c
--TERMneqTSQUASH {c} {z} ()

--TERMneqTTRUNC : {c : Term} {z : Term} → ¬ TERM z ≡ TTRUNC c
--TERMneqTTRUNC {c} {z} ()

TERMneqNOWRITE : {z : Term} → ¬ TERM z ≡ NOWRITE
TERMneqNOWRITE {z} ()

TERMneqNOREAD : {z : Term} → ¬ TERM z ≡ NOREAD
TERMneqNOREAD {z} ()

TERMneqLOWER : {c : Term} {z : Term} → ¬ TERM z ≡ LOWER c
TERMneqLOWER {c} {z} ()

TERMneqSHRINK : {c : Term} {z : Term} → ¬ TERM z ≡ SHRINK c
TERMneqSHRINK {c} {z} ()

TERMneqUNIV : {n : ℕ} {z : Term} → ¬ TERM z ≡ UNIV n
TERMneqUNIV {n} {z} ()


typeSysConds-TERM-tsym : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                            (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                            (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                            → eqTypes u w B A
typeSysConds-TERM-tsym u w A B t1 t2 x x₁ x₂ = EQTTERM t2 t1 x₁ x (□NATeq-sym {w} {t1} {t2} x₂)


typeSysConds-TERM-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                           (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                           (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                            → eqTypesTrans u w A B
{-# TERMINATING #-}
--typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂)
  rewrite #TERMinj {u1} {t2} (#⇛-val-det {_} {B} tt tt y x₁)
  = EQTTERM t1 u2 x y₁ (□NATeq-trans {w} {t1} {t2} {u2} x₂ y₂)
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

--typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-TERM-ttrans
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C eqt



typeSysConds-TERM-isym : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                         (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                         (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                         → eqInTypeSym u {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
typeSysConds-TERM-isym u w A B t1 t2 x x₁ x₂ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                       → TERMeq w' t1 t2)
    h w1 e1 z = z



typeSysConds-TERM-itrans : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                           (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                           (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                            → eqInTypeTrans u {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
typeSysConds-TERM-itrans u w A B t1 t2 x x₁ x₂ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → TERMeq w' t1 t2
                      → TERMeq w' t1 t2
                      → TERMeq w' t1 t2)
    aw w1 e1 a b = a



typeSysConds-TERM-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                          (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                          (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                          → eqInTypeExtL1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y))
--typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y))
--typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y))
--typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u1} {t1} (#⇛-val-det {_} {A} tt tt y x)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t1 u2
                        → TERMeq w' t1 u2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t1} tt tt z₁ d₁)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t1} tt tt d₁ c₁)
      = n , c₁ , z₂ , c₃
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

--typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extl1
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                          (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                          (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                          → eqInTypeExtL2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u2} {t1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' u1 t1
                        → TERMeq w' u1 t1)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t1} tt tt z₂ d₁)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t1} tt tt d₁ c₁)
      = n , z₁ , c₁ , c₃

typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

--typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extl2
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                          (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                          (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                          → eqInTypeExtR1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u2} {t2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' u1 t2
                        → TERMeq w' u1 t2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t2} tt tt z₂ d₂)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t2} tt tt d₂ c₂)
      = n , z₁ , c₂ , c₃

typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

--typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extr1
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                          (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                          (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                          → eqInTypeExtR2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u1} {t2} (#⇛-val-det {_} {B} tt tt y x₁)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t2 u2
                       → TERMeq w' t2 u2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t2} tt tt z₁ d₂)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t2} tt tt d₂ c₂)
      = n , c₂ , z₂ , c₃

typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

--typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extr2
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                             (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                             (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                             → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y))
--typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y))
--typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y))
--typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u1} {t1} (#⇛-val-det {_} {A} tt tt y x)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 u2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t1 u2
                        → TERMeq w' t1 t2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t1} tt tt z₁ d₁)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t1} tt tt d₁ c₁)
      = n , c₁ , d₂ , c₃

typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

--typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM t1 t2 (⇛-mon e' x) (⇛-mon e' x₁) (Mod.↑□ M x₂ e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevl1
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' t1 t2))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)
 -- (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TERM-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                             (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                             (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                             → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u2} {t1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' u1 t1
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' u1 t1
                        → TERMeq w' t1 t2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t1} tt tt z₂ d₁)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t1} tt tt d₁ c₂)
      = n , c₂ , d₂ , c₃

typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

--typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM t1 t2 (⇛-mon e' x) (⇛-mon e' x₁) (Mod.↑□ M x₂ e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevl2
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' t1 t2))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TERM-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                             (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                             (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                             → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u2} {t2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' u1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' u1 t2
                        → TERMeq w' t1 t2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t2} tt tt z₂ d₂)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t2} tt tt d₂ c₂)
      = n , d₁ , c₂ , c₃

typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

--typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM t1 t2 (⇛-mon e' x) (⇛-mon e' x₁) (Mod.↑□ M x₂ e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevr1
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' t1 t2 ))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TERM-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                             (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                             (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                             → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
{-# TERMINATING #-}
--typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTNOENC y y₁) f g eqi = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTTERM u1 u2 y y₁ y₂) f g eqi
  rewrite #TERMinj {u1} {t2} (#⇛-val-det {_} {B} tt tt y x₁)
  = ∀𝕎-□Func3 aw eqi x₂ y₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t2 u2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t2 u2
                        → TERMeq w' t1 t2)
    aw w1 e1 (n , c₁ , c₂ , c₃) (m , d₁ , d₂) (k , z₁ , z₂)
      rewrite #NUMinj {k} {m} (#⇛-val-det {_} {t2} tt tt z₁ d₂)
            | #NUMinj {m} {n} (#⇛-val-det {_} {t2} tt tt d₂ c₁)
      = n , d₁ , c₁ , c₃

typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTNOWRITE y y₁) f g eqi = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTNOREAD y y₁) f g eqi = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTPARTIAL A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

--typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM t1 t2 (⇛-mon e' x) (⇛-mon e' x₁) (Mod.↑□ M x₂ e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevr2
        u w1 A B t1 t2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (Mod.↑□ M x₂ e1)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' t1 t2))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TERM : (u : univs) (w : 𝕎·) (A B t1 t2 a b : CTerm)
                   (bx : □· w (λ w' _ → #strongMonEq w' t1 t2))
                      → A #⇛ #TERM t1 at w
                      → B #⇛ #TERM t2 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → TERMeq w' t1 t2)
{-# TERMINATING #-}
--eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTNOENC x x₁) ei = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTTERM u1 u2 x x₁ x₂) ei
  rewrite #TERMinj {u1} {t1} (#⇛-val-det {_} {A} tt tt x c₁)
        | #TERMinj {u2} {t2} (#⇛-val-det {_} {B} tt tt x₁ c₂)
  = ∀𝕎-□Func3 aw ei bx x₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → TERMeq w' t1 t2)
    aw w1 e1 p q r = p

eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTNOWRITE x x₁) ei = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTNOREAD x x₁) ei = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTPARTIAL A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

--eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B t1 t2 a b bx c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → TERMeq w'' t1 t2))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TERM
        u w1 A B t1 t2 a b (Mod.↑□ M bx e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TERMeq w'' t1 t2))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



eqInType-⇛-TERM2 : (u : 𝕌) (w : 𝕎·) (A B t1 t2 a b : CTerm)
                    (bx : □· w (λ w' _ → #strongMonEq w' t1 t2))
                       → A #⇛ #TERM t1 at w
                       → B #⇛ #TERM t2 at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → TERMeq w' t1 t2)
{-# TERMINATING #-}
--eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOENC x x₁) ei = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTTERM u1 u2 x x₁ x₂) ei
  rewrite #TERMinj {u1} {t1} (#⇛-val-det {_} {A} tt tt x c₁)
        | #TERMinj {u2} {t2} (#⇛-val-det {_} {B} tt tt x₁ c₂)
  = ∀𝕎-□Func3 aw ei bx x₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → TERMeq w' t1 t2)
    aw w1 e1 p q r = p

eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOWRITE x x₁) ei = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOREAD x x₁) ei = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTPARTIAL A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

--eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B t1 t2 a b bx c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → TERMeq w'' t1 t2))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TERM2
        u w1 A B t1 t2 a b (Mod.↑□ M bx e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TERMeq w'' t1 t2))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TERM-rev : (u : univs) (w : 𝕎·) (A B t1 t2 a b : CTerm)
                       (bx : □· w (λ w' _ → #strongMonEq w' t1 t2))
                          → A #⇛ #TERM t1 at w
                          → B #⇛ #TERM t2 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → TERMeq w' t1 t2)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
--eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTNOENC x x₁) ei = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTTERM u1 u2 x x₁ x₂) ei
  rewrite #TERMinj {u1} {t1} (#⇛-val-det {_} {A} tt tt x c₁)
        | #TERMinj {u2} {t2} (#⇛-val-det {_} {B} tt tt x₁ c₂)
  = ∀𝕎-□Func3 aw ei bx x₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → TERMeq w' t1 t2)
    aw w1 e1 p q r = p

eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTNOWRITE x x₁) ei = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTNOREAD x x₁) ei = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTPARTIAL A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

--eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B t1 t2 a b bx c₁ c₂ (EQTBAR x) ei =
  ∀𝕎-□-□'₀ W M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TERM-rev
        u w1 A B t1 t2 a b (Mod.↑□ M bx e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → TERMeq w' t1 t2) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-TERM-rev2 : (u : 𝕌) (w : 𝕎·) (A B t1 t2 a b : CTerm)
                       (bx : □· w (λ w' _ → #strongMonEq w' t1 t2))
                           → A #⇛ #TERM t1 at w
                           → B #⇛ #TERM t2 at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → TERMeq w' t1 t2)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
--eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (TERMneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOENC x x₁) ei = ⊥-elim (TERMneqNOENC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTTERM u1 u2 x x₁ x₂) ei
  rewrite #TERMinj {u1} {t1} (#⇛-val-det {_} {A} tt tt x c₁)
        | #TERMinj {u2} {t2} (#⇛-val-det {_} {B} tt tt x₁ c₂)
  = ∀𝕎-□Func3 aw ei bx x₂
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → #strongMonEq w' t1 t2
                        → TERMeq w' t1 t2)
    aw w1 e1 p q r = p

eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOWRITE x x₁) ei = ⊥-elim (TERMneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTNOREAD x x₁) ei = ⊥-elim (TERMneqNOREAD (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTPARTIAL A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqPARTIAL (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

--eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B t1 t2 a b bx c₁ c₂ (EQTBAR x) ei =
  ∀𝕎-□-□'₀ W M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TERM-rev2
        u w1 A B t1 t2 a b (Mod.↑□ M bx e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → TERMeq w' t1 t2) e1)
        j = Mod.↑□ M ei e1



typeSysConds-TERM-local : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                          (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                          (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                           → eqInTypeLocal (EQTTERM t1 t2 x x₁ x₂)
typeSysConds-TERM-local u w A B t1 t2 x x₁ x₂ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → TERMeq w'' t1 t2))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → TERMeq w'' t1 t2)
        aw' = eqInType-⇛-TERM u w1 A B t1 t2 a b (Mod.↑□ M x₂ e1) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → TERMeq w' t1 t2
                                → (x₂ : w ⊑· w') → TERMeq w' t1 t2)
        aw'' w' e' p x₂ = p



typeSysConds-TERM : (u : univs) (w : 𝕎·) (A B : CTerm) (t1 t2 : CTerm)
                    (x : A #⇛ #TERM t1 at w) (x₁ : B #⇛ #TERM t2 at w)
                    (x₂ : □· w (λ w' _ → #strongMonEq w' t1 t2))
                    → TSP {u} (EQTTERM t1 t2 x x₁ x₂)
typeSysConds-TERM u w A B t1 t2 x x₁ x₂ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TERM-tsym u w A B t1 t2 x x₁ x₂

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TERM-ttrans u w A B t1 t2 x x₁ x₂

    isym : eqInTypeSym u {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    isym = typeSysConds-TERM-isym u w A B t1 t2 x x₁ x₂

    itrans : eqInTypeTrans u {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    itrans = typeSysConds-TERM-itrans u w A B t1 t2 x x₁ x₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextl1 = typeSysConds-TERM-extl1 u w A B t1 t2 x x₁ x₂

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextl2 = typeSysConds-TERM-extl2 u w A B t1 t2 x x₁ x₂

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextr1 = typeSysConds-TERM-extr1 u w A B t1 t2 x x₁ x₂

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextr2 = typeSysConds-TERM-extr2 u w A B t1 t2 x x₁ x₂

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextrl1 = typeSysConds-TERM-extrevl1 u w A B t1 t2 x x₁ x₂

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextrl2 = typeSysConds-TERM-extrevl2 u w A B t1 t2 x x₁ x₂

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextrr1 = typeSysConds-TERM-extrevr1 u w A B t1 t2 x x₁ x₂

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTERM t1 t2 x x₁ x₂)
    iextrr2 = typeSysConds-TERM-extrevr2 u w A B t1 t2 x x₁ x₂

    local : eqInTypeLocal (EQTTERM t1 t2 x x₁ x₂)
    local = typeSysConds-TERM-local u w A B t1 t2 x x₁ x₂
\end{code}
