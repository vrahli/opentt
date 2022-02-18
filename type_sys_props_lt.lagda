\begin{code}

--open import bar
--module type_sys_props_lt (bar : Bar) where

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


module type_sys_props_lt {L : Level} (W : PossibleWorlds {L})
                         (C : Choice) (M : Compatible {L} W C) (P : Progress {L} W C M) (G : GetChoice {L} W C M)
                         (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(M)(G)
open import bar(W)
open import barI(W)(C)(M)(P)
open import forcing(W)(C)(M)(P)(G)(E)
open import props0(W)(C)(M)(P)(G)(E)
open import ind2(W)(C)(M)(P)(G)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
LTneqNAT : {u v : Term} → ¬ LT u v ≡ NAT
LTneqNAT {u} {v} ()

LTneqQNAT : {u v : Term} → ¬ LT u v ≡ QNAT
LTneqQNAT {u} {v} ()

LTneqQLT : {u v : Term} {c d : Term} → ¬ LT u v ≡ QLT c d
LTneqQLT {u} {v} {c} {d} ()

LTneqFREE : {u v : Term} → ¬ LT u v ≡ FREE
LTneqFREE {u} {v} ()

LTneqPI : {u v : Term} {c d : Term} → ¬ LT u v ≡ PI c d
LTneqPI {u} {v} {c} {d} ()

LTneqSUM : {u v : Term} {c d : Term} → ¬ LT u v ≡ SUM c d
LTneqSUM {u} {v} {c} {d} ()

LTneqSET : {u v : Term} {c d : Term} → ¬ LT u v ≡ SET c d
LTneqSET {u} {v} {c} {d} ()

LTneqUNION : {u v : Term} {c d : Term} → ¬ LT u v ≡ UNION c d
LTneqUNION {u} {v} {c} {d} ()

LTneqEQ : {u v : Term} {c d e : Term} → ¬ LT u v ≡ EQ c d e
LTneqEQ {u} {v} {c} {d} {e} ()

LTneqTSQUASH : {u v : Term} {c : Term} → ¬ LT u v ≡ TSQUASH c
LTneqTSQUASH {u} {v} {c} ()

LTneqLIFT : {u v : Term} {c : Term} → ¬ LT u v ≡ LIFT c
LTneqLIFT {u} {v} {c} ()

LTneqDUM : {u v : Term} {c : Term} → ¬ LT u v ≡ DUM c
LTneqDUM {u} {v} {c} ()

LTneqFFDEFS : {u v : Term} {c d : Term} → ¬ LT u v ≡ FFDEFS c d
LTneqFFDEFS {u} {v} {c} {d} ()

LTneqLOWER : {u v : Term} {c : Term} → ¬ LT u v ≡ LOWER c
LTneqLOWER {u} {v} {c} ()

LTneqSHRINK : {u v : Term} {c : Term} → ¬ LT u v ≡ SHRINK c
LTneqSHRINK {u} {v} {c} ()

LTneqUNIV : {u v : Term} {n : ℕ} → ¬ LT u v ≡ UNIV n
LTneqUNIV {u} {v} {n} ()


typeSysConds-LT-ttrans : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                         (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅)
  rewrite LTinj1 (⇛-val-det tt tt y x₁)
        | LTinj2 (⇛-val-det tt tt y x₁)
  = EQTLT a1 c2 b1 d2 x y₁ (strongMonEq-trans s x₄) (strongMonEq-trans s₁ x₅)
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 c2 d1 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) = ⊥-elim (LTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) =
  EQTBAR (Bar.∀𝕎-□Func barI aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 z =
      typeSysConds-LT-ttrans
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z




typeSysConds-LT-extl1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                          (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                          → eqInTypeExtL1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y x)
        | LTinj2 (⇛-val-det tt tt y x) = eqi
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y))
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.∀𝕎-□-□' barI y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} =
      typeSysConds-LT-extl1
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑□ barI eqi e1)

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

        c : inbar' w y (λ w' e' z → eqInType u w' z a b)
        c = loc-∀𝕎-inOpenBar-inOpenBar' y
        --c = Bar.∀𝕎-□-□' barI aw y
--}



typeSysConds-LT-extl2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                          (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                          → eqInTypeExtL2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y₁ x)
        | LTinj2 (⇛-val-det tt tt y₁ x)
  = strongMonEq-preserves-inbar {_} {a1} {b1} {c1} {d1} x₄ x₅ eqi
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.∀𝕎-□-□' barI y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} =
      typeSysConds-LT-extl2
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑□ barI eqi e1)



typeSysConds-LT-extr1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y₁ x₁)
        | LTinj2 (⇛-val-det tt tt y₁ x₁)
  = strongMonEq-preserves-inbar {_} {a1} {b1} {c1} {d1} (strongMonEq-trans x₄ (strongMonEq-sym s)) ((strongMonEq-trans x₅ (strongMonEq-sym s₁))) eqi
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.∀𝕎-□-□' barI y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} =
      typeSysConds-LT-extr1
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑□ barI eqi e1)



typeSysConds-LT-extr2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y x₁)
        | LTinj2 (⇛-val-det tt tt y x₁)
  = strongMonEq-preserves-inbar {_} {a1} {b1} {a2} {b2} (strongMonEq-sym s) (strongMonEq-sym s₁) eqi
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.∀𝕎-□-□' barI y aw
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b)
    aw w1 e1 z {--at--} =
      typeSysConds-LT-extr2
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑□ barI eqi e1)



typeSysConds-LT-extrevl1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                           → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y x)
        | LTinj2 (⇛-val-det tt tt y x)
  = strongMonEq-preserves-inbar {_} {a1} {b1} {a1} {b1} (strongMonEq-refl x₄) (strongMonEq-refl x₅) eqi
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y))
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.□-idem
    barI
    (Bar.∀𝕎-□'-□ barI y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Bar.□ barI w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z {--at--} eqz =
      typeSysConds-LT-extrevl1
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Bar.□ barI w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z {--at--} eqz = Bar.∀𝕎-□Func barI (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



typeSysConds-LT-extrevl2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                           → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y₁ x)
        | LTinj2 (⇛-val-det tt tt y₁ x)
  = strongMonEq-preserves-inbar {_} {c1} {d1} {a1} {b1} (strongMonEq-sym x₄) (strongMonEq-sym x₅) eqi
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.□-idem
    barI
    (Bar.∀𝕎-□'-□ barI y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Bar.□ barI w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z {--at--} eqz =
      typeSysConds-LT-extrevl2
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C A) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Bar.□ barI w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z {--at--} eqz = Bar.∀𝕎-□Func barI (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)




typeSysConds-LT-extrevr1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                            (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y₁ x₁)
        | LTinj2 (⇛-val-det tt tt y₁ x₁)
  = strongMonEq-preserves-inbar {_} {c1} {d1} {a1} {b1} (strongMonEq-trans s (strongMonEq-sym x₄)) (strongMonEq-trans s₁ (strongMonEq-sym x₅)) eqi
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.□-idem
    barI
    (Bar.∀𝕎-□'-□ barI y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Bar.□ barI w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z {--at--} eqz =
      typeSysConds-LT-extrevr1
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' C B) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Bar.□ barI w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z {--at--} eqz = Bar.∀𝕎-□Func barI (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



typeSysConds-LT-extrevr2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                           → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite LTinj1 (⇛-val-det tt tt y x₁)
        | LTinj2 (⇛-val-det tt tt y x₁)
  = strongMonEq-preserves-inbar {_} {a2} {b2} {a1} {b1} s s₁ eqi
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (LTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV i p c₁ c₂) a b eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLIFT A1 A2 y y₁ eqtA exta) a b eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.□-idem
    barI
    (Bar.∀𝕎-□'-□ barI y aw eqi)
  where
    aw0 : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                          → Bar.□ barI w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z {--at--} eqz =
      typeSysConds-LT-extrevr2
        u w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' B C) {--(at : atbar y w' e' x)--} → eqInType u w' x a b
                         → Bar.□ barI w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z {--at--} eqz = Bar.∀𝕎-□Func barI (λ w1 e1 z x → z) (aw0 w1 e1 z {--at--} eqz)



eqInType-⇛-LT : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 a b : CTerm)
                 → A #⇛ #LT a1 b1 at w
                 → B #⇛ #LT a2 b2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → inbar w (λ w' e → #lift-<NUM-pair w' a1 b1)
{-# TERMINATING #-}
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (LTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (LTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei
  rewrite LTinj1 (⇛-val-det tt tt x c₁)
        | LTinj2 (⇛-val-det tt tt x c₁) = ei
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (LTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (LTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (LTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (LTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (LTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (LTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (LTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (LTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (LTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA extA) ei = ⊥-elim (LTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTBAR x) ei =
  Bar.□-idem barI (Bar.∀𝕎-□'-□ barI x aw ei)
  where
    aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →  eqInType u w' z a b → inbar w' (λ w'' _ → #lift-<NUM-pair w'' a1 b1))
    aw0 w1 e1 z {--at--} eqi = eqInType-⇛-LT u w1 A B a1 b1 a2 b2 a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) z eqi

    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →  eqInType u w' z a b → inbar w' (λ w'' _ → w ⊑· w'' → #lift-<NUM-pair w'' a1 b1))
    aw w1 e1 z {--at--} eqi = Bar.∀𝕎-□Func barI (λ w' e' s x → s) (aw0 w1 e1 z {--at--} eqi)




eqInType-⇛-LT-rev : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 a b : CTerm)
                     → A #⇛ #LT a1 b1 at w
                     → B #⇛ #LT a2 b2 at w
                     → (eqt : eqTypes u w A B)
                     → inbar w (λ w' e → #lift-<NUM-pair w' a1 b1)
                     → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (LTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (LTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei
  rewrite LTinj1 (⇛-val-det tt tt x c₁)
        | LTinj2 (⇛-val-det tt tt x c₁) = ei
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (LTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (LTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (LTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (LTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (LTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (LTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (LTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (LTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (LTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA extA) ei = ⊥-elim (LTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ (EQTBAR x) ei =
  Bar.∀𝕎-□-□' barI x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w' e' z {--at--} = eqInType-⇛-LT-rev u w' A B a1 b1 a2 b2 a b (⇛-mon e' c₁) (⇛-mon e' c₂) z (Bar.↑□ barI ei e')




typeSysConds-LT-local : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #LT a1 b1 at w) (x₁ : B #⇛ #LT a2 b2 at w)
                        (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                        → eqInTypeLocal {u} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-local u w A B a1 b1 a2 b2 x x₁ s s₁ a b i j =
  Bar.□-idem barI (Bar.∀𝕎-□'-□ barI i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--} → eqInType u w' z a b → inbar w' (λ w'' e → w ⊑· w'' → #lift-<NUM-pair w'' a1 b1))
    aw w1 e1 z {--at--} ei = Bar.∀𝕎-□Func barI (λ w' e' s x → s) aw'
      where
        aw' : inbar w1 (λ w' e → #lift-<NUM-pair w' a1 b1)
        aw' = eqInType-⇛-LT u w1 A B a1 b1 a2 b2 a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-LT : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                  (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                  (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                  → TSP {u} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT u w A B a1 b1 a2 b2 x x₁ s s₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTLT a2 a1 b2 b1 x₁ x (strongMonEq-sym s) (strongMonEq-sym s₁)

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁

    isym : eqInTypeSym u {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    isym a b eqi = eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    itrans a b c eqi₁ eqi₂ = eqi₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextl1 = typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextl2 = typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextr1 = typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextr2 = typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextrl1 = typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextrl2 = typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextrr1 = typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    iextrr2 = typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁

    local : eqInTypeLocal (EQTLT a1 a2 b1 b2 x x₁ s s₁)
    local = typeSysConds-LT-local u w A B a1 b1 a2 b2 x x₁ s s₁
\end{code}
