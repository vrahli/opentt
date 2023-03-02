\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module type_sys_props_qnat (bar : Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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
open import newChoice
open import mod


module type_sys_props_tnat {L : Level} (L' : Level) (W : PossibleWorlds {L}) (M : Mod L' W)
                           (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                           (X : ChoiceExt W C)
                           (N : NewChoice W C K G)
                           (E : Extensionality 0ℓ (lsuc (lsuc L) ⊔ lsuc (lsuc L')))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(L')(W)
open import barI(L')(W)(M)--(C)(K)(P)
open import forcing(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)

-- open import Function.Bundles
-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
\end{code}



\begin{code}[hide]
-- TNAT
TNATneqNAT : ¬ TNAT ≡ NAT
TNATneqNAT ()

TNATneqQNAT : ¬ TNAT ≡ QNAT
TNATneqQNAT ()

TNATneqLT : {c d : Term} → ¬ TNAT ≡ LT c d
TNATneqLT {c} {d} ()

TNATneqQLT : {c d : Term} → ¬ TNAT ≡ QLT c d
TNATneqQLT {c} {d} ()

TNATneqFREE : ¬ TNAT ≡ FREE
TNATneqFREE ()

TNATneqPI : {c : Term} {d : Term} → ¬ TNAT ≡ PI c d
TNATneqPI {c} {d} ()

TNATneqSUM : {c : Term} {d : Term} → ¬ TNAT ≡ SUM c d
TNATneqSUM {c} {d} ()

TNATneqSET : {c : Term} {d : Term} → ¬ TNAT ≡ SET c d
TNATneqSET {c} {d} ()

TNATneqTUNION : {c : Term} {d : Term} → ¬ TNAT ≡ TUNION c d
TNATneqTUNION {c} {d} ()

TNATneqISECT : {c : Term} {d : Term} → ¬ TNAT ≡ ISECT c d
TNATneqISECT {c} {d} ()

TNATneqUNION : {c : Term} {d : Term} → ¬ TNAT ≡ UNION c d
TNATneqUNION {c} {d} ()

TNATneqQTUNION : {c : Term} {d : Term} → ¬ TNAT ≡ QTUNION c d
TNATneqQTUNION {c} {d} ()

TNATneqEQ : {c d e : Term} → ¬ TNAT ≡ EQ c d e
TNATneqEQ {c} {d} {e} ()

TNATneqTSQUASH : {c : Term} → ¬ TNAT ≡ TSQUASH c
TNATneqTSQUASH {c} ()

TNATneqTTRUNC : {c : Term} → ¬ TNAT ≡ TTRUNC c
TNATneqTTRUNC {c} ()

TNATneqTCONST : {c : Term} → ¬ TNAT ≡ TCONST c
TNATneqTCONST {c} ()

TNATneqSUBSING : {c : Term} → ¬ TNAT ≡ SUBSING c
TNATneqSUBSING {c} ()

TNATneqPURE : ¬ TNAT ≡ PURE
TNATneqPURE ()

TNATneqLIFT : {c : Term} → ¬ TNAT ≡ LIFT c
TNATneqLIFT {c} ()

TNATneqDUM : {c : Term} → ¬ TNAT ≡ DUM c
TNATneqDUM {c} ()

TNATneqFFDEFS : {c d : Term} → ¬ TNAT ≡ FFDEFS c d
TNATneqFFDEFS {c} {d} ()

TNATneqLOWER : {c : Term} → ¬ TNAT ≡ LOWER c
TNATneqLOWER {c} ()

TNATneqSHRINK : {c : Term} → ¬ TNAT ≡ SHRINK c
TNATneqSHRINK {c} ()

TNATneqUNIV : {n : ℕ} → ¬ TNAT ≡ UNIV n
TNATneqUNIV {n} ()



typeSysConds-TNAT-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                           (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                           → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTQNAT y y₁) = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTTNAT y y₁) = EQTTNAT x y₁
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (TNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTFREE y y₁) = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (TNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (TNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTPURE y y₁) = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-ttrans u w A B x x₁ C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 z = typeSysConds-TNAT-ttrans u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z




typeSysConds-TNAT-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtL1 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x y))
--typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extl1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-TNAT-extl1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)

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



typeSysConds-TNAT-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x y₁))
--typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extl2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-TNAT-extl2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)



typeSysConds-TNAT-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extr1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-TNAT-extr1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)



typeSysConds-TNAT-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extr2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.∀𝕎-□-□' M y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} = typeSysConds-TNAT-extr2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Mod.↑□ M eqi e1)



typeSysConds-TNAT-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x y))
--typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TNAT-extrevl1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-TNAT-extrevl1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



typeSysConds-TNAT-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x y₁))
--typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TNAT-extrevl2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-TNAT-extrevl2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)




typeSysConds-TNAT-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TNAT-extrevr1 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-TNAT-extrevr1 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



typeSysConds-TNAT-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTTNAT y y₁) a b eqi = eqi
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTTRUNC A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTCONST A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTSUBSING A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTPURE y y₁) a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTLIFT A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TNAT-extrevr2 u w A B x x₁ C (EQTBAR y) a b eqi =
  Mod.□-idem M
    (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
    aw0 w1 e1 z {--at--} eqz = typeSysConds-TNAT-extrevr2 u w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
    aw w1 e1 z {--at--} eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



eqInType-⇛-TNAT : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                  → A #⇛ #TNAT at w
                  → B #⇛ #TNAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → □· w (λ w' e → TNATeq w' a b)
{-# TERMINATING #-}
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TNATneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ei
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TNATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TNATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TNATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (TNATneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (TNATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (TNATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTTRUNC A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTCONST A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTSUBSING A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TNATneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (TNATneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →  eqInType u w' z a b → □· w' (λ w'' _ → TNATeq w'' a b))
    aw0 w1 e1 z {--at--} eqi = eqInType-⇛-TNAT u w1 A B a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) z eqi

    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →  eqInType u w' z a b → □· w' (λ w'' _ → w ⊑· w'' → TNATeq w'' a b))
    aw w1 e1 z {--at--} eqi = Mod.∀𝕎-□Func M (λ w' e' s x → s) (aw0 w1 e1 z {--at--} eqi)




eqInType-⇛-TNAT-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #TNAT at w
                       → B #⇛ #TNAT at w
                       → (eqt : eqTypes u w A B)
                       → □· w (λ w' _ → TNATeq w' a b)
                       → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TNATneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTTNAT x x₁) ei = ei
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TNATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TNATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TNATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (TNATneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (TNATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (TNATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTTRUNC A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTCONST A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTSUBSING A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TNATneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (TNATneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA extA) ei = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w' e' z {--at--} = eqInType-⇛-TNAT-rev u w' A B a b (⇛-mon e' c₁) (⇛-mon e' c₂) z (Mod.↑□ M ei e')




typeSysConds-TNAT-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                          (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                          → eqInTypeLocal {u} (EQTTNAT x x₁)
typeSysConds-TNAT-local u w A B x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--} → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → TNATeq w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
      where
        aw' : □· w1 (λ w' e → TNATeq w' a b)
        aw' = eqInType-⇛-TNAT u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-TNAT : (u : univs) (w : 𝕎·) (A B : CTerm)
                    (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                    → TSP {u} (EQTTNAT x x₁)
typeSysConds-TNAT u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTTNAT x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TNAT-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTTNAT x x₁)
    isym a b eqi = □TNATeq-sym {w} {a} {b} eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTTNAT x x₁)
    itrans a b c eqi₁ eqi₂ = □TNATeq-trans {w} {a} {b} {c} eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextl1 = typeSysConds-TNAT-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextl2 = typeSysConds-TNAT-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextr1 = typeSysConds-TNAT-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextr2 = typeSysConds-TNAT-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextrl1 = typeSysConds-TNAT-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextrl2 = typeSysConds-TNAT-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextrr1 = typeSysConds-TNAT-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTNAT x x₁)
    iextrr2 = typeSysConds-TNAT-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTTNAT x x₁)
    local = typeSysConds-TNAT-local u w A B x x₁
\end{code}
