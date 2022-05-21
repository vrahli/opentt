\begin{code}

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


module type_sys_props_nn {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
NNneqNAT : {a : Term} → ¬ (NN a) ≡ NAT
NNneqNAT {a} ()

NNneqQNAT : {a : Term} → ¬ (NN a) ≡ QNAT
NNneqQNAT {a} ()

NNneqLT : {a : Term} {c d : Term} → ¬ (NN a) ≡ LT c d
NNneqLT {a} {c} {d} ()

NNneqQLT : {a : Term} {c d : Term} → ¬ (NN a) ≡ QLT c d
NNneqQLT {a} {c} {d} ()

NNneqFREE : {a : Term} → ¬ (NN a) ≡ FREE
NNneqFREE {a} ()

NNneqPI : {a : Term} {c : Term} {d : Term} → ¬ (NN a) ≡ PI c d
NNneqPI {a} {c} {d} ()

NNneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (NN a) ≡ SUM c d
NNneqSUM {a} {c} {d} ()

NNneqSET : {a : Term} {c : Term} {d : Term} → ¬ (NN a) ≡ SET c d
NNneqSET {a} {c} {d} ()

NNneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (NN a) ≡ TUNION c d
NNneqTUNION {a} {c} {d} ()

NNneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (NN a) ≡ UNION c d
NNneqUNION {a} {c} {d} ()

NNneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (NN a) ≡ QTUNION c d
NNneqQTUNION {a} {c} {d} ()

NNneqEQ : {a : Term} {c d e : Term} → ¬ (NN a) ≡ EQ c d e
NNneqEQ {a} {c} {d} {e} ()

NNneqDUM : {a : Term} {c : Term} → ¬ (NN a) ≡ DUM c
NNneqDUM {a} {c} ()

NNneqFFDEFS : {a : Term} {c d : Term} → ¬ (NN a) ≡ FFDEFS c d
NNneqFFDEFS {a} {c} {d} ()

NNneqSUBSING : {a : Term} {b : Term} → ¬ (NN a) ≡ SUBSING b
NNneqSUBSING {a} {b} ()

NNneqLIFT : {a : Term} {c : Term} → ¬ (NN a) ≡ LIFT c
NNneqLIFT {a} {c} ()

NNneqTSQUASH : {a : Term} {c : Term} → ¬ (NN a) ≡ TSQUASH c
NNneqTSQUASH {a} {c} ()

NNneqTTRUNC : {a : Term} {c : Term} → ¬ (NN a) ≡ TTRUNC c
NNneqTTRUNC {a} {c} ()

NNneqTCONST : {a : Term} {c : Term} → ¬ (NN a) ≡ TCONST c
NNneqTCONST {a} {c} ()

NNneqLOWER : {a : Term} {c : Term} → ¬ (NN a) ≡ LOWER c
NNneqLOWER {a} {c} ()

NNneqSHRINK : {a : Term} {c : Term} → ¬ (NN a) ≡ SHRINK c
NNneqSHRINK {a} {c} ()

NNneqUNIV : {a : Term} {n : ℕ} → ¬ (NN a) ≡ UNIV n
NNneqUNIV {a} {n} ()


typeSysConds-NN-tsym : (u : univs) (w : 𝕎·) (A B t : CTerm)
                            (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                            → eqTypes u w B A
typeSysConds-NN-tsym u w A B t x x₁ = EQTNN t x₁ x



typeSysConds-NN-ttrans : (u : univs) (w : 𝕎·) (A B t : CTerm)
                              (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTNAT y y₁) = ⊥-elim (NNneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTQNAT y y₁) = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (NNneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (NNneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTFREE y y₁) = ⊥-elim (NNneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NNneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NNneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (NNneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (NNneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NNneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTNN t₁ y y₁)
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {B} tt tt y x₁)
  = EQTNN t x y₁
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-NN-ttrans u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (NNneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-NN-ttrans u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-ttrans u w A B t x x₁ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-NN-ttrans
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C eqt



typeSysConds-NN-isym : (u : univs) (w : 𝕎·) (A B t : CTerm)
                            (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                            → eqInTypeSym u {_} {A} {B} (EQTNN t x x₁)
typeSysConds-NN-isym u w A B t x x₁ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → NNeq t f g
                       → NNeq t g f)
    h w1 e1 p = p



typeSysConds-NN-itrans : (u : univs) (w : 𝕎·) (A B t : CTerm)
                              (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTNN t x x₁)
typeSysConds-NN-itrans u w A B t x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → NNeq t f g
                      → NNeq t g h
                      → NNeq t f h)
    aw w1 e1 p₁ p₂ = p₁



typeSysConds-NN-extl1 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                             (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                        → NNeq t f g)
    aw w1 e1 p = p
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-NN-extl1 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-NN-extl1 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x y))
typeSysConds-NN-extl1 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NN-extl1
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-NN-extl2 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                             (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' → NNeq t f g
                       → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extl2 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-NN-extl2 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-NN-extl2 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extl2 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NN-extl2
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-NN-extr1 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                             (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                        → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extr1 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-NN-extr1 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-NN-extr1 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extr1 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NN-extr1
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-NN-extr2 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                             (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                       → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extr2 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-NN-extr2 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-NN-extr2 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extr2 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-NN-extr2
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-NN-extrevl1 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                                (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                        → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x y))
typeSysConds-NN-extrevl1 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNN t (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NN-extrevl1
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NNeq t f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)
 -- (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-NN-extrevl2 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                                (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                        → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-NN-extrevl2 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNN t (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NN-extrevl2
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NNeq t f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-NN-extrevr1 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                                (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                       → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NN-extrevr1 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNN t (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NN-extrevr1
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NNeq t f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)



typeSysConds-NN-extrevr2 : (u : univs) (w : 𝕎·) (A B t : CTerm)
                                (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNN t x x₁)
{-# TERMINATING #-}
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTNAT y y₁) f g eqi = ⊥-elim (NNneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTQNAT y y₁) f g eqi = ⊥-elim (NNneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (NNneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTFREE y y₁) f g eqi = ⊥-elim (NNneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (NNneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTNN t₁ y y₁) f g eqi
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t f g
                       → NNeq t f g)
    aw w1 e1 p = p

typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (NNneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (NNneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (NNneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-NN-extrevr2 u w A B t x x₁ C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTNN t (⇛-mon e' x) (⇛-mon e' x₁)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-NN-extrevr2
        u w1 A B t
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → NNeq t f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-NN : (u : univs) (w : 𝕎·) (A B t a b : CTerm)
                      → A #⇛ #NN t at w
                      → B #⇛ #NN t at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → NNeq t a b)
{-# TERMINATING #-}
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NNneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NNneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NNneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NNneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTNN t₁ x x₁) ei
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt x c₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t a b
                        → NNeq t a b)
    aw w1 e1 p = p

eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NNneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NNneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NNneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN u w A B t a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → NNeq t a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-NN
        u w1 A B t a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → NNeq t a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-NN2 : (u : 𝕌) (w : 𝕎·) (A B t a b : CTerm)
                       → A #⇛ #NN t at w
                       → B #⇛ #NN t at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → NNeq t a b)
{-# TERMINATING #-}
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NNneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NNneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NNneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NNneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTNN t₁ x x₁) ei
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt x c₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t a b
                         → NNeq t a b)
    aw w1 e1 p = p

eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NNneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NNneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NNneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN2 u w A B t a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → NNeq t a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-NN2
        u w1 A B t a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → NNeq t a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (λ w1 e1 z e → z) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-NN-rev : (u : univs) (w : 𝕎·) (A B t a b : CTerm)
                          → A #⇛ #NN t at w
                          → B #⇛ #NN t at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → NNeq t a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NNneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NNneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NNneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NNneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTNN t₁ x x₁) ei
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt x c₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t a b
                        → NNeq t a b)
    aw w1 e1 p = p

eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NNneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NNneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NNneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev u w A B t a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-NN-rev
        u w1 A B t a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → NNeq t a b) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-NN-rev2 : (u : 𝕌) (w : 𝕎·) (A B t a b : CTerm)
                           → A #⇛ #NN t at w
                           → B #⇛ #NN t at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → NNeq t a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (NNneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NNneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NNneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NNneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (NNneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (NNneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTNN t₁ x x₁) ei
  rewrite #NNinj {t₁} {t} (#⇛-val-det {_} {A} tt tt x c₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → NNeq t a b
                        → NNeq t a b)
    aw w1 e1 p = p

eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (NNneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (NNneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NNneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (NNneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NNneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (NNneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NN-rev2 u w A B t a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-NN-rev2
        u w1 A B t a b
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → NNeq t a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-NN-local : (u : univs) (w : 𝕎·) (A B t : CTerm)
                             (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                             → eqInTypeLocal (EQTNN t x x₁)
typeSysConds-NN-local u w A B t x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → NNeq t a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → NNeq t a b)
        aw' = eqInType-⇛-NN u w1 A B t a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → NNeq t a b
                                → (x₂ : w ⊑· w') → NNeq t a b)
        aw'' w' e' p x₂ = p



typeSysConds-NN : (u : univs) (w : 𝕎·) (A B t : CTerm)
                       (x : A #⇛ #NN t at w) (x₁ : B #⇛ #NN t at w)
                       → TSP {u} (EQTNN t x x₁)
typeSysConds-NN u w A B t x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-NN-tsym u w A B t x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NN-ttrans u w A B t x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTNN t x x₁)
    isym = typeSysConds-NN-isym u w A B t x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNN t x x₁)
    itrans = typeSysConds-NN-itrans u w A B t x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNN t x x₁)
    iextl1 = typeSysConds-NN-extl1 u w A B t x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNN t x x₁)
    iextl2 = typeSysConds-NN-extl2 u w A B t x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNN t x x₁)
    iextr1 = typeSysConds-NN-extr1 u w A B t x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNN t x x₁)
    iextr2 = typeSysConds-NN-extr2 u w A B t x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNN t x x₁)
    iextrl1 = typeSysConds-NN-extrevl1 u w A B t x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNN t x x₁)
    iextrl2 = typeSysConds-NN-extrevl2 u w A B t x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNN t x x₁)
    iextrr1 = typeSysConds-NN-extrevr1 u w A B t x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNN t x x₁)
    iextrr2 = typeSysConds-NN-extrevr2 u w A B t x x₁

    local : eqInTypeLocal (EQTNN t x x₁)
    local = typeSysConds-NN-local u w A B t x x₁
\end{code}
