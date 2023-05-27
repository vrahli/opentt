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


module type_sys_props_noseq {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
NOSEQneqPURE : ¬ NOSEQ ≡ PURE
NOSEQneqPURE ()

NOSEQneqTERM : {c : Term} → ¬ NOSEQ ≡ TERM c
NOSEQneqTERM {c} ()

NOSEQneqNAT : ¬ NOSEQ ≡ NAT
NOSEQneqNAT ()

NOSEQneqQNAT : ¬ NOSEQ ≡ QNAT
NOSEQneqQNAT ()

NOSEQneqTNAT : ¬ NOSEQ ≡ TNAT
NOSEQneqTNAT ()

NOSEQneqLT : {c d : Term} → ¬ NOSEQ ≡ LT c d
NOSEQneqLT {c} {d} ()

NOSEQneqQLT : {c d : Term} → ¬ NOSEQ ≡ QLT c d
NOSEQneqQLT {c} {d} ()

NOSEQneqFREE : ¬ NOSEQ ≡ FREE
NOSEQneqFREE ()

NOSEQneqPI : {c : Term} {d : Term} → ¬ NOSEQ ≡ PI c d
NOSEQneqPI {c} {d} ()

NOSEQneqW : {c : Term} {d : Term} → ¬ NOSEQ ≡ WT c d
NOSEQneqW {c} {d} ()

NOSEQneqM : {c : Term} {d : Term} → ¬ NOSEQ ≡ MT c d
NOSEQneqM {c} {d} ()

NOSEQneqSUM : {c : Term} {d : Term} → ¬ NOSEQ ≡ SUM c d
NOSEQneqSUM {c} {d} ()

NOSEQneqSET : {c : Term} {d : Term} → ¬ NOSEQ ≡ SET c d
NOSEQneqSET {c} {d} ()

NOSEQneqISECT : {c : Term} {d : Term} → ¬ NOSEQ ≡ ISECT c d
NOSEQneqISECT {c} {d} ()

NOSEQneqTUNION : {c : Term} {d : Term} → ¬ NOSEQ ≡ TUNION c d
NOSEQneqTUNION {c} {d} ()

NOSEQneqUNION : {c : Term} {d : Term} → ¬ NOSEQ ≡ UNION c d
NOSEQneqUNION {c} {d} ()

NOSEQneqQTUNION : {c : Term} {d : Term} → ¬ NOSEQ ≡ QTUNION c d
NOSEQneqQTUNION {c} {d} ()

NOSEQneqEQ : {c d e : Term} → ¬ NOSEQ ≡ EQ c d e
NOSEQneqEQ {c} {d} {e} ()

NOSEQneqDUM : {c : Term} → ¬ NOSEQ ≡ DUM c
NOSEQneqDUM {c} ()

NOSEQneqFFDEFS : {c d : Term} → ¬ NOSEQ ≡ FFDEFS c d
NOSEQneqFFDEFS {c} {d} ()

NOSEQneqSUBSING : {b : Term} → ¬ NOSEQ ≡ SUBSING b
NOSEQneqSUBSING {b} ()

NOSEQneqLIFT : {c : Term} → ¬ NOSEQ ≡ LIFT c
NOSEQneqLIFT {c} ()

NOSEQneqTSQUASH : {c : Term} → ¬ NOSEQ ≡ TSQUASH c
NOSEQneqTSQUASH {c} ()

NOSEQneqTTRUNC : {c : Term} → ¬ NOSEQ ≡ TTRUNC c
NOSEQneqTTRUNC {c} ()

NOSEQneqTCONST : {c : Term} → ¬ NOSEQ ≡ TCONST c
NOSEQneqTCONST {c} ()

NOSEQneqLOWER : {c : Term} → ¬ NOSEQ ≡ LOWER c
NOSEQneqLOWER {c} ()

NOSEQneqSHRINK : {c : Term} → ¬ NOSEQ ≡ SHRINK c
NOSEQneqSHRINK {c} ()

NOSEQneqUNIV : {n : ℕ} → ¬ NOSEQ ≡ UNIV n
NOSEQneqUNIV {n} ()


typeSysConds-NOSEQ-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                            → eqTypes u w B A
typeSysConds-NOSEQ-tsym u w A B x x₁ = EQTNOSEQ x₁ x



typeSysConds-NOSEQ-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTQNAT y y₁) = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTTNAT y y₁) = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTFREE y y₁) = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTPURE y y₁) = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTNOSEQ y y₁)
  = EQTNOSEQ x y₁
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-ttrans u w A B x x₁ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-NOSEQ-ttrans
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C eqt



typeSysConds-NOSEQ-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                            → eqInTypeSym u {_} {A} {B} (EQTNOSEQ x x₁)
typeSysConds-NOSEQ-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → NOSEQeq f g
                       → NOSEQeq g f)
    h w1 e1 (lift (n1 , n2 , m1 , m2)) = lift (n2 , n1 , m2 , m1)



typeSysConds-NOSEQ-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTNOSEQ x x₁)
typeSysConds-NOSEQ-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → NOSEQeq f g
                      → NOSEQeq g h
                      → NOSEQeq f h)
    aw w1 e1 (lift (p₁ , p₂ , p₃ , p₄)) (lift (q₁ , q₂ , q₃ , q₄)) = lift (p₁ , q₂ , p₃ , q₄)



typeSysConds-NOSEQ-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                        → NOSEQeq f g)
    aw w1 e1 p = p
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extl1 u w A B x x₁ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NOSEQ-extl1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-NOSEQ-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' → NOSEQeq f g
                       → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extl2 u w A B x x₁ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NOSEQ-extl2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-NOSEQ-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                        → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extr1 u w A B x x₁ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NOSEQ-extr1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-NOSEQ-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                       → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extr2 u w A B x x₁ C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NOSEQ-extr2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-NOSEQ-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                        → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x y))
typeSysConds-NOSEQ-extrevl1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNOSEQ (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NOSEQ-extrevl1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NOSEQeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)
 -- (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-NOSEQ-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                        → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-NOSEQ-extrevl2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNOSEQ (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NOSEQ-extrevl2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NOSEQeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-NOSEQ-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                       → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NOSEQ-extrevr1 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNOSEQ (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NOSEQ-extrevr1
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NOSEQeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-NOSEQ-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
{-# TERMINATING #-}
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTTNAT y y₁) f g eqi = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqW (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTPURE y y₁) f g eqi = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTNOSEQ y y₁) f g eqi
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq f g
                       → NOSEQeq f g)
    aw w1 e1 p = p

typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-NOSEQ-extrevr2 u w A B x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNOSEQ (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NOSEQ-extrevr2
        u w1 A B
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NOSEQeq f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-NOSEQ : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #NOSEQ at w
                      → B #⇛ #NOSEQ at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → NOSEQeq a b)
{-# TERMINATING #-}
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTNOSEQ x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq a b
                        → NOSEQeq a b)
    aw w1 e1 p = p

eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → NOSEQeq a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-NOSEQ
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → NOSEQeq a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-NOSEQ2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #NOSEQ at w
                       → B #⇛ #NOSEQ at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → NOSEQeq a b)
{-# TERMINATING #-}
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTNOSEQ x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq a b
                         → NOSEQeq a b)
    aw w1 e1 p = p

eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ2 u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → NOSEQeq a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-NOSEQ2
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → NOSEQeq a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-NOSEQ-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #NOSEQ at w
                          → B #⇛ #NOSEQ at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → NOSEQeq a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTNOSEQ x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq a b
                        → NOSEQeq a b)
    aw w1 e1 p = p

eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev u w A B a b c₁ c₂ (EQTBAR x) ei =
  ∀𝕎-□-□'₀ W M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-NOSEQ-rev
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → NOSEQeq a b) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-NOSEQ-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #NOSEQ at w
                           → B #⇛ #NOSEQ at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → NOSEQeq a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NOSEQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NOSEQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (NOSEQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NOSEQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NOSEQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei = ⊥-elim (NOSEQneqTERM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NOSEQneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NOSEQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (NOSEQneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTNOSEQ x x₁) ei
  = Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NOSEQeq a b
                        → NOSEQeq a b)
    aw w1 e1 p = p

eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NOSEQneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NOSEQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NOSEQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NOSEQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NOSEQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NOSEQ-rev2 u w A B a b c₁ c₂ (EQTBAR x) ei =
  ∀𝕎-□-□'₀ W M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-NOSEQ-rev2
        u w1 A B a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → NOSEQeq a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-NOSEQ-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                             → eqInTypeLocal (EQTNOSEQ x x₁)
typeSysConds-NOSEQ-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → NOSEQeq a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → NOSEQeq a b)
        aw' = eqInType-⇛-NOSEQ u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → NOSEQeq a b
                                → (x₂ : w ⊑· w') → NOSEQeq a b)
        aw'' w' e' p x₂ = p



typeSysConds-NOSEQ : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #NOSEQ at w) (x₁ : B #⇛ #NOSEQ at w)
                       → TSP {u} (EQTNOSEQ x x₁)
typeSysConds-NOSEQ u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-NOSEQ-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NOSEQ-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTNOSEQ x x₁)
    isym = typeSysConds-NOSEQ-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNOSEQ x x₁)
    itrans = typeSysConds-NOSEQ-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextl1 = typeSysConds-NOSEQ-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextl2 = typeSysConds-NOSEQ-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextr1 = typeSysConds-NOSEQ-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextr2 = typeSysConds-NOSEQ-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextrl1 = typeSysConds-NOSEQ-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextrl2 = typeSysConds-NOSEQ-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextrr1 = typeSysConds-NOSEQ-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOSEQ x x₁)
    iextrr2 = typeSysConds-NOSEQ-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTNOSEQ x x₁)
    local = typeSysConds-NOSEQ-local u w A B x x₁
\end{code}
