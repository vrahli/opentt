\begin{code}

--open import bar
--module type_sys_props_qnat (bar : Bar) where

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
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
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
open import mod


module type_sys_props_qnat {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                           (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                           (X : ChoiceExt W C)
                           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(E)

-- open import Function.Bundles
-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
\end{code}



\begin{code}[hide]
-- QNAT
QNATneqNAT : ¬ QNAT ≡ NAT
QNATneqNAT ()

QNATneqLT : {c d : Term} → ¬ QNAT ≡ LT c d
QNATneqLT {c} {d} ()

QNATneqQLT : {c d : Term} → ¬ QNAT ≡ QLT c d
QNATneqQLT {c} {d} ()

QNATneqFREE : ¬ QNAT ≡ FREE
QNATneqFREE ()

QNATneqPI : {c : Term} {d : Term} → ¬ QNAT ≡ PI c d
QNATneqPI {c} {d} ()

QNATneqSUM : {c : Term} {d : Term} → ¬ QNAT ≡ SUM c d
QNATneqSUM {c} {d} ()

QNATneqSET : {c : Term} {d : Term} → ¬ QNAT ≡ SET c d
QNATneqSET {c} {d} ()

QNATneqTUNION : {c : Term} {d : Term} → ¬ QNAT ≡ TUNION c d
QNATneqTUNION {c} {d} ()

QNATneqUNION : {c : Term} {d : Term} → ¬ QNAT ≡ UNION c d
QNATneqUNION {c} {d} ()

QNATneqQTUNION : {c : Term} {d : Term} → ¬ QNAT ≡ QTUNION c d
QNATneqQTUNION {c} {d} ()

QNATneqEQ : {c d e : Term} → ¬ QNAT ≡ EQ c d e
QNATneqEQ {c} {d} {e} ()

QNATneqTSQUASH : {c : Term} → ¬ QNAT ≡ TSQUASH c
QNATneqTSQUASH {c} ()

QNATneqTTRUNC : {c : Term} → ¬ QNAT ≡ TTRUNC c
QNATneqTTRUNC {c} ()

QNATneqTCONST : {c : Term} → ¬ QNAT ≡ TCONST c
QNATneqTCONST {c} ()

QNATneqLIFT : {c : Term} → ¬ QNAT ≡ LIFT c
QNATneqLIFT {c} ()

QNATneqDUM : {c : Term} → ¬ QNAT ≡ DUM c
QNATneqDUM {c} ()

QNATneqFFDEFS : {c d : Term} → ¬ QNAT ≡ FFDEFS c d
QNATneqFFDEFS {c} {d} ()

QNATneqLOWER : {c : Term} → ¬ QNAT ≡ LOWER c
QNATneqLOWER {c} ()

QNATneqSHRINK : {c : Term} → ¬ QNAT ≡ SHRINK c
QNATneqSHRINK {c} ()

QNATneqUNIV : {n : ℕ} → ¬ QNAT ≡ UNIV n
QNATneqUNIV {n} ()



typeSysConds-QNAT-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                           (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                           → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTQNAT y y₁) = EQTQNAT x y₁
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTFREE y y₁) = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u w A B x x₁ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 z = typeSysConds-QNAT-ttrans u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z




typeSysConds-QNAT-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtL1 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-QNAT-extl1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)

{-- c
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b)
        aw w1 e1 z = iextl1 w1 (⇛-mon e1 x) C z a b (Bar.□-mon barI e1 eqi)

        f : wPred w
        f = λ w' _ → eqTypes u w' A C

        g : wPredDep f
        g = λ w' e' (x : eqTypes u w' A C) → eqInType u w' x a b

        loc-∀𝕎-inOpenBar-inOpenBar' : (i : inOpenBar w f) → inOpenBar' w i g
        loc-∀𝕎-inOpenBar-inOpenBar' i w1 e1 = w2 , extRefl w2 , λ w3 e3 z → aw w3 z (h0 w3 (extTrans e3 (extRefl w2)) z)
          where
            w2 : 𝕎·
            w2 = fst (i w1 e1)

            e2 : w2 ≽ w1
            e2 = fst (snd (i w1 e1))

            h0 : ∀𝕎 w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
            h0 = snd (snd (i w1 e1))

        c : □·' w y (λ w' e' z → eqInType u w' z a b)
        c = loc-∀𝕎-inOpenBar-inOpenBar' y
        --c = Mod.∀𝕎-□-□' M aw y
--}



typeSysConds-QNAT-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-QNAT-extl2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)



typeSysConds-QNAT-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-QNAT-extr1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)



typeSysConds-QNAT-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-QNAT-extr2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)



typeSysConds-QNAT-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → #weakMonEq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-QNAT-extrevl1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → #weakMonEq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



typeSysConds-QNAT-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → #weakMonEq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-QNAT-extrevl2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → #weakMonEq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)




typeSysConds-QNAT-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → #weakMonEq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-QNAT-extrevr1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → #weakMonEq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



typeSysConds-QNAT-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → #weakMonEq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-QNAT-extrevr2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → #weakMonEq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



eqInType-⇛-QNAT : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                  → A #⇛ #QNAT at w
                  → B #⇛ #QNAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → □· w (λ w' e → #weakMonEq w' a b)
{-# TERMINATING #-}
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QNATneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ei
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QNATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QNATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QNATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (QNATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (QNATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTTRUNC A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTCONST A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (QNATneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →  eqInType u w' z a b → □· w' (λ w'' _ → #weakMonEq w'' a b))
    aw0 w1 e1 z {--at--} eqi = eqInType-⇛-QNAT u w1 A B a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) z eqi

    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →  eqInType u w' z a b → □· w' (λ w'' _ → w ⊑· w'' → #weakMonEq w'' a b))
    aw w1 e1 z {--at--} eqi = Mod.∀𝕎-□Func M (λ w' e' s x → s) (aw0 w1 e1 z {--at--} eqi)




eqInType-⇛-QNAT-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #QNAT at w
                       → B #⇛ #QNAT at w
                       → (eqt : eqTypes u w A B)
                       → □· w (λ w' _ → #weakMonEq w' a b)
                       → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QNATneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ei
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QNATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QNATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QNATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (QNATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (QNATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTTRUNC A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTCONST A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (QNATneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w' e' z {--at--} = eqInType-⇛-QNAT-rev u w' A B a b (⇛-mon e' c₁) (⇛-mon e' c₂) z (Mod.↑□ M ei e')




typeSysConds-QNAT-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                          (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                          → eqInTypeLocal {u} (EQTQNAT x x₁)
typeSysConds-QNAT-local u w A B x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--} → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → #weakMonEq w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
      where
        aw' : □· w1 (λ w' e → #weakMonEq w' a b)
        aw' = eqInType-⇛-QNAT u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-QNAT : (u : univs) (w : 𝕎·) (A B : CTerm)
                    (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                    → TSP {u} (EQTQNAT x x₁)
typeSysConds-QNAT u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTQNAT x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-QNAT-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTQNAT x x₁)
    isym a b eqi = □·-weakMonEq-sym eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTQNAT x x₁)
    itrans a b c eqi₁ eqi₂ = □·-weakMonEq-trans eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextl1 = typeSysConds-QNAT-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextl2 = typeSysConds-QNAT-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextr1 = typeSysConds-QNAT-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextr2 = typeSysConds-QNAT-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextrl1 = typeSysConds-QNAT-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextrl2 = typeSysConds-QNAT-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextrr1 = typeSysConds-QNAT-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTQNAT x x₁)
    iextrr2 = typeSysConds-QNAT-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTQNAT x x₁)
    local = typeSysConds-QNAT-local u w A B x x₁
\end{code}
