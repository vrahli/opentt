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


module type_sys_props_term {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
TERMneqNAT : ¬ TERM ≡ NAT
TERMneqNAT ()

TERMneqQNAT : ¬ TERM ≡ QNAT
TERMneqQNAT ()

TERMneqTNAT : ¬ TERM ≡ TNAT
TERMneqTNAT ()

TERMneqPURE : ¬ TERM ≡ PURE
TERMneqPURE ()

TERMneqLT : {c d : Term} → ¬ TERM ≡ LT c d
TERMneqLT {c} {d} ()

TERMneqQLT : {c d : Term} → ¬ TERM ≡ QLT c d
TERMneqQLT {c} {d} ()

TERMneqFREE : ¬ TERM ≡ FREE
TERMneqFREE ()

TERMneqPI : {c : Term} {d : Term} → ¬ TERM ≡ PI c d
TERMneqPI {c} {d} ()

TERMneqW : {c : Term} {d : Term} → ¬ TERM ≡ WT c d
TERMneqW {c} {d} ()

TERMneqM : {c : Term} {d : Term} → ¬ TERM ≡ MT c d
TERMneqM {c} {d} ()

TERMneqSUM : {c : Term} {d : Term} → ¬ TERM ≡ SUM c d
TERMneqSUM {c} {d} ()

TERMneqSET : {c : Term} {d : Term} → ¬ TERM ≡ SET c d
TERMneqSET {c} {d} ()

TERMneqISECT : {c : Term} {d : Term} → ¬ TERM ≡ ISECT c d
TERMneqISECT {c} {d} ()

TERMneqTUNION : {c : Term} {d : Term} → ¬ TERM ≡ TUNION c d
TERMneqTUNION {c} {d} ()

TERMneqUNION : {c : Term} {d : Term} → ¬ TERM ≡ UNION c d
TERMneqUNION {c} {d} ()

TERMneqQTUNION : {c : Term} {d : Term} → ¬ TERM ≡ QTUNION c d
TERMneqQTUNION {c} {d} ()

TERMneqEQ : {c d e : Term} → ¬ TERM ≡ EQ c d e
TERMneqEQ {c} {d} {e} ()

TERMneqDUM : {c : Term} → ¬ TERM ≡ DUM c
TERMneqDUM {c} ()

TERMneqFFDEFS : {c d : Term} → ¬ TERM ≡ FFDEFS c d
TERMneqFFDEFS {c} {d} ()

TERMneqSUBSING : {b : Term} → ¬ TERM ≡ SUBSING b
TERMneqSUBSING {b} ()

TERMneqLIFT : {c : Term} → ¬ TERM ≡ LIFT c
TERMneqLIFT {c} ()

TERMneqTSQUASH : {c : Term} → ¬ TERM ≡ TSQUASH c
TERMneqTSQUASH {c} ()

TERMneqTTRUNC : {c : Term} → ¬ TERM ≡ TTRUNC c
TERMneqTTRUNC {c} ()

TERMneqTCONST : {c : Term} → ¬ TERM ≡ TCONST c
TERMneqTCONST {c} ()

TERMneqLOWER : {c : Term} → ¬ TERM ≡ LOWER c
TERMneqLOWER {c} ()

TERMneqSHRINK : {c : Term} → ¬ TERM ≡ SHRINK c
TERMneqSHRINK {c} ()

TERMneqUNIV : {n : ℕ} → ¬ TERM ≡ UNIV n
TERMneqUNIV {n} ()


typeSysConds-TERM-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                            → eqTypes u w B A
typeSysConds-TERM-tsym u w A B x x₁ = EQTTERM x₁ x



typeSysConds-TERM-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTQNAT y y₁) = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTTNAT y y₁) = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTFREE y y₁) = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTPURE y y₁) = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTTERM y y₁)
  = EQTTERM x y₁
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-ttrans u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TERM-ttrans u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-ttrans u w A B x x₁ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-TERM-ttrans
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C eqt



typeSysConds-TERM-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                            → eqInTypeSym u {_} {A} {B} (EQTTERM x x₁)
typeSysConds-TERM-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → TERMeq w' f g
                       → TERMeq w' g f)
    h w1 e1 (n , c₁ , c₂ , p) = n , c₂ , c₁ , p -- (lift (n1 , n2)) = lift (n2 , n1)



typeSysConds-TERM-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTTERM x x₁)
typeSysConds-TERM-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → TERMeq w' f g
                      → TERMeq w' g h
                      → TERMeq w' f h)
    aw w1 e1 (n , c₁ , c₂ , p) (m , d₁ , d₂ , q)
      rewrite NUMinj (⇓-val-det tt tt (lower (d₁ w1 (⊑-refl· w1))) (lower (c₂ w1 (⊑-refl· w1))))
      = n , c₁ , d₂ , p



typeSysConds-TERM-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                        → TERMeq w' f g)
    aw w1 e1 p = p
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-TERM-extl1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TERM-extl1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TERM-extl1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extl1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' → TERMeq w' f g
                       → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extl2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extl2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TERM-extl2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extl2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extl2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                        → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extr1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extr1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TERM-extr1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extr1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extr1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TERM-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                       → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extr2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extr2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TERM-extr2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extr2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TERM-extr2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-TERM-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                        → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TERM-extrevl1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevl1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)
 -- (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TERM-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                        → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TERM-extrevl2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevl2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TERM-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                       → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TERM-extrevr1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevr1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TERM-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTERM x x₁)
{-# TERMINATING #-}
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (TERMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TERMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (TERMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TERMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (TERMneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTTERM y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' f g
                       → TERMeq w' f g)
    aw w1 e1 p = p

typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TERMneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TERM-extrevr2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTERM (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TERM-extrevr2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TERMeq w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TERM : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #TERM at w
                      → B #⇛ #TERM at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → TERMeq w' a b)
{-# TERMINATING #-}
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTTERM x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' a b
                        → TERMeq w' a b)
    aw w1 e1 p = p

eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TERMneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → TERMeq w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TERM
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TERMeq w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TERM2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #TERM at w
                       → B #⇛ #TERM at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → TERMeq w' a b)
{-# TERMINATING #-}
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTTERM x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' a b
                         → TERMeq w' a b)
    aw w1 e1 p = p

eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TERMneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM2 u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → TERMeq w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TERM2
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TERMeq w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TERM-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #TERM at w
                          → B #⇛ #TERM at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → TERMeq w' a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTTERM x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' a b
                        → TERMeq w' a b)
    aw w1 e1 p = p

eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TERMneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TERM-rev
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → TERMeq w' a b) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-TERM-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #TERM at w
                           → B #⇛ #TERM at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → TERMeq w' a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TERMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TERMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TERMneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TERMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TERMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TERMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TERMneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TERMneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTTERM x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TERMeq w' a b
                        → TERMeq w' a b)
    aw w1 e1 p = p

eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TERMneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TERMneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TERMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TERMneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TERMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TERMneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TERM-rev2 u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TERM-rev2
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → TERMeq w' a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-TERM-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                             → eqInTypeLocal (EQTTERM x x₁)
typeSysConds-TERM-local u w A B x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → TERMeq w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → TERMeq w'' a b)
        aw' = eqInType-⇛-TERM u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → TERMeq w' a b
                                → (x₂ : w ⊑· w') → TERMeq w' a b)
        aw'' w' e' p x₂ = p



typeSysConds-TERM : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #TERM at w) (x₁ : B #⇛ #TERM at w)
                       → TSP {u} (EQTTERM x x₁)
typeSysConds-TERM u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TERM-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TERM-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTTERM x x₁)
    isym = typeSysConds-TERM-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTTERM x x₁)
    itrans = typeSysConds-TERM-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTTERM x x₁)
    iextl1 = typeSysConds-TERM-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTTERM x x₁)
    iextl2 = typeSysConds-TERM-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTTERM x x₁)
    iextr1 = typeSysConds-TERM-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTTERM x x₁)
    iextr2 = typeSysConds-TERM-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTERM x x₁)
    iextrl1 = typeSysConds-TERM-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTERM x x₁)
    iextrl2 = typeSysConds-TERM-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTERM x x₁)
    iextrr1 = typeSysConds-TERM-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTERM x x₁)
    iextrr2 = typeSysConds-TERM-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTTERM x x₁)
    local = typeSysConds-TERM-local u w A B x x₁
\end{code}
