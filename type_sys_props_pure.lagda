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


module type_sys_props_pure {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
PUREneqNAT : ¬ PURE ≡ NAT
PUREneqNAT ()

PUREneqQNAT : ¬ PURE ≡ QNAT
PUREneqQNAT ()

PUREneqTNAT : ¬ PURE ≡ TNAT
PUREneqTNAT ()

PUREneqLT : {c d : Term} → ¬ PURE ≡ LT c d
PUREneqLT {c} {d} ()

PUREneqQLT : {c d : Term} → ¬ PURE ≡ QLT c d
PUREneqQLT {c} {d} ()

PUREneqFREE : ¬ PURE ≡ FREE
PUREneqFREE ()

PUREneqPI : {c : Term} {d : Term} → ¬ PURE ≡ PI c d
PUREneqPI {c} {d} ()

PUREneqW : {c : Term} {d : Term} → ¬ PURE ≡ WT c d
PUREneqW {c} {d} ()

PUREneqM : {c : Term} {d : Term} → ¬ PURE ≡ MT c d
PUREneqM {c} {d} ()

PUREneqSUM : {c : Term} {d : Term} → ¬ PURE ≡ SUM c d
PUREneqSUM {c} {d} ()

PUREneqSET : {c : Term} {d : Term} → ¬ PURE ≡ SET c d
PUREneqSET {c} {d} ()

PUREneqISECT : {c : Term} {d : Term} → ¬ PURE ≡ ISECT c d
PUREneqISECT {c} {d} ()

PUREneqTUNION : {c : Term} {d : Term} → ¬ PURE ≡ TUNION c d
PUREneqTUNION {c} {d} ()

PUREneqUNION : {c : Term} {d : Term} → ¬ PURE ≡ UNION c d
PUREneqUNION {c} {d} ()

PUREneqQTUNION : {c : Term} {d : Term} → ¬ PURE ≡ QTUNION c d
PUREneqQTUNION {c} {d} ()

PUREneqEQ : {c d e : Term} → ¬ PURE ≡ EQ c d e
PUREneqEQ {c} {d} {e} ()

PUREneqDUM : {c : Term} → ¬ PURE ≡ DUM c
PUREneqDUM {c} ()

PUREneqFFDEFS : {c d : Term} → ¬ PURE ≡ FFDEFS c d
PUREneqFFDEFS {c} {d} ()

PUREneqSUBSING : {b : Term} → ¬ PURE ≡ SUBSING b
PUREneqSUBSING {b} ()

PUREneqLIFT : {c : Term} → ¬ PURE ≡ LIFT c
PUREneqLIFT {c} ()

PUREneqTSQUASH : {c : Term} → ¬ PURE ≡ TSQUASH c
PUREneqTSQUASH {c} ()

PUREneqTTRUNC : {c : Term} → ¬ PURE ≡ TTRUNC c
PUREneqTTRUNC {c} ()

PUREneqTCONST : {c : Term} → ¬ PURE ≡ TCONST c
PUREneqTCONST {c} ()

PUREneqLOWER : {c : Term} → ¬ PURE ≡ LOWER c
PUREneqLOWER {c} ()

PUREneqSHRINK : {c : Term} → ¬ PURE ≡ SHRINK c
PUREneqSHRINK {c} ()

PUREneqUNIV : {n : ℕ} → ¬ PURE ≡ UNIV n
PUREneqUNIV {n} ()


typeSysConds-PURE-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                            → eqTypes u w B A
typeSysConds-PURE-tsym u w A B x x₁ = EQTPURE x₁ x



typeSysConds-PURE-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTQNAT y y₁) = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTTNAT y y₁) = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (PUREneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTFREE y y₁) = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (PUREneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (PUREneqW (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (PUREneqM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (PUREneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTPURE y y₁)
  = EQTPURE x y₁
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-PURE-ttrans u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-PURE-ttrans u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-ttrans u w A B x x₁ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-PURE-ttrans
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C eqt



typeSysConds-PURE-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                            → eqInTypeSym u {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → PUREeq f g
                       → PUREeq g f)
    h w1 e1 (lift (n1 , n2)) = lift (n2 , n1)



typeSysConds-PURE-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → PUREeq f g
                      → PUREeq g h
                      → PUREeq f h)
    aw w1 e1 (lift (p₁ , p₂)) (lift (q₁ , q₂)) = lift (p₁ , q₂)



typeSysConds-PURE-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                        → PUREeq f g)
    aw w1 e1 p = p
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-PURE-extl1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-PURE-extl1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x y))
typeSysConds-PURE-extl1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PURE-extl1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-PURE-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' → PUREeq f g
                       → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extl2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-PURE-extl2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-PURE-extl2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extl2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PURE-extl2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-PURE-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                        → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extr1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-PURE-extr1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-PURE-extr1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extr1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PURE-extr1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-PURE-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                       → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extr2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-PURE-extr2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-PURE-extr2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extr2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PURE-extr2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-PURE-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                        → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x y))
typeSysConds-PURE-extrevl1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTPURE (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PURE-extrevl1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → PUREeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)
 -- (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-PURE-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                        → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-PURE-extrevl2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTPURE (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PURE-extrevl2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → PUREeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-PURE-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                       → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PURE-extrevr1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTPURE (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PURE-extrevr1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → PUREeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-PURE-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTPURE x x₁)
{-# TERMINATING #-}
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTPURE y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq f g
                       → PUREeq f g)
    aw w1 e1 p = p

typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-PURE-extrevr2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTPURE (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PURE-extrevr2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → PUREeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-PURE : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #PURE at w
                      → B #⇛ #PURE at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → PUREeq a b)
{-# TERMINATING #-}
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PUREneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PUREneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PUREneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTPURE x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a b
                        → PUREeq a b)
    aw w1 e1 p = p

eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (PUREneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → PUREeq a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-PURE
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → PUREeq a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-PURE2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #PURE at w
                       → B #⇛ #PURE at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → PUREeq a b)
{-# TERMINATING #-}
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PUREneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PUREneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PUREneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTPURE x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a b
                         → PUREeq a b)
    aw w1 e1 p = p

eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (PUREneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE2 u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → PUREeq a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-PURE2
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → PUREeq a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-PURE-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #PURE at w
                          → B #⇛ #PURE at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → PUREeq a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PUREneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PUREneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PUREneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTPURE x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a b
                        → PUREeq a b)
    aw w1 e1 p = p

eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (PUREneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-PURE-rev
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → PUREeq a b) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-PURE-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #PURE at w
                           → B #⇛ #PURE at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → PUREeq a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PUREneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PUREneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PUREneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PUREneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTPURE x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a b
                        → PUREeq a b)
    aw w1 e1 p = p

eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (PUREneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (PUREneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PUREneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-PURE-rev2
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → PUREeq a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-PURE-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeLocal (EQTPURE x x₁)
typeSysConds-PURE-local u w A B x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → PUREeq a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → PUREeq a b)
        aw' = eqInType-⇛-PURE u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → PUREeq a b
                                → (x₂ : w ⊑· w') → PUREeq a b)
        aw'' w' e' p x₂ = p



typeSysConds-PURE : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                       → TSP {u} (EQTPURE x x₁)
typeSysConds-PURE u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-PURE-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-PURE-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTPURE x x₁)
    isym = typeSysConds-PURE-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTPURE x x₁)
    itrans = typeSysConds-PURE-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextl1 = typeSysConds-PURE-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextl2 = typeSysConds-PURE-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextr1 = typeSysConds-PURE-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextr2 = typeSysConds-PURE-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrl1 = typeSysConds-PURE-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrl2 = typeSysConds-PURE-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrr1 = typeSysConds-PURE-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrr2 = typeSysConds-PURE-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTPURE x x₁)
    local = typeSysConds-PURE-local u w A B x x₁
\end{code}
