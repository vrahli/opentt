\begin{code}


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
open import mod


module type_sys_props_union {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                            (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                            (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

--open import theory (bar)
--open import props0 (bar)
--open import ind2 (bar)
--open import terms (bar)
\end{code}



\begin{code}[hide]
INLneqINR : {a b : Term} → ¬ INL a ≡ INR b
INLneqINR {a} {b} ()


UNIONneqNAT : {a b : Term} → ¬ (UNION a b) ≡ NAT
UNIONneqNAT {a} {b} ()

UNIONneqQNAT : {a b : Term} → ¬ (UNION a b) ≡ QNAT
UNIONneqQNAT {a} {b} ()

UNIONneqLT : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ LT c d
UNIONneqLT {a} {b} {c} {d} ()

UNIONneqQLT : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ QLT c d
UNIONneqQLT {a} {b} {c} {d} ()

UNIONneqFREE : {a b : Term} → ¬ (UNION a b) ≡ FREE
UNIONneqFREE {a} {b} ()

UNIONneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (UNION a b) ≡ EQ c d e
UNIONneqEQ {a} {b} {c} {d} {e} ()

UNIONneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ PI c d
UNIONneqPI {a} {b} {c} {d} ()

UNIONneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ SET c d
UNIONneqSET {a} {b} {c} {d} ()

UNIONneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ TUNION c d
UNIONneqTUNION {a} {b} {c} {d} ()

UNIONneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ SUM c d
UNIONneqSUM {a} {b} {c} {d} ()

UNIONneqTSQUASH : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ TSQUASH c
UNIONneqTSQUASH {a} {b} {c} ()

UNIONneqTCONST : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ TCONST c
UNIONneqTCONST {a} {b} {c} ()

UNIONneqLIFT : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ LIFT c
UNIONneqLIFT {a} {b} {c} ()

UNIONneqDUM : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ DUM c
UNIONneqDUM {a} {b} {c} ()

UNIONneqFFDEFS : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ FFDEFS c d
UNIONneqFFDEFS {a} {b} {c} {d} ()

UNIONneqLOWER : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ LOWER c
UNIONneqLOWER {a} {b} {c} ()

UNIONneqSHRINK : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ SHRINK c
UNIONneqSHRINK {a} {b} {c} ()

UNIONneqUNIV : {a b : Term} {n : ℕ} → ¬ (UNION a b) ≡ UNIV n
UNIONneqUNIV {a} {b} {n} ()



typeSysConds-UNION-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqTypes u w B A
typeSysConds-UNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTUNION A2 B2 A1 B1 x₁ x syma symb exta' extb'
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : ∀𝕎 w (λ w' e → eqTypes u w' B2 B1)
    symb w1 e1 = TSP.tsym (indb w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) A2 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) A2 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (indb w₁ e)) a b)
    extb' a b w' e1 e2 ei = TSP.extl2 (indb w' e2) B2 (TSP.tsym (indb w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqtb w' e1) a b
        ei1 = TSP.extrevl2 (indb w' e1) B2 (TSP.tsym (indb w' e1)) a b ei

        ei2 : eqInType u w' (eqtb w' e2) a b
        ei2 = extb a b w' e1 e2 ei1


typeSysConds-UNION-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                            (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                            (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                            → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite #UNIONinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #UNIONinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTUNION A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 D2)
    eqb w1 e1 = TSP.ttrans (indb w1 e1) D2 (eqtb0 w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) C2 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqb w₁ e) a b)
    extb' a b w' e1 e2 ei = TSP.extl1 (indb w' e2) D2 (eqb w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqtb w' e1) a b
        ei1 = TSP.extrevl1 (indb w' e1) D2 (eqb w' e1) a b ei

        ei2 : eqInType u w' (eqtb w' e2) a b
        ei2 = extb a b w' e1 e2 ei1

typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-UNION-ttrans
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C eqt



typeSysConds-UNION-isym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqInTypeSym u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                  → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' g f)
    h w1 e1 (a , b , inj₁ (c₁ , c₂ , eqa)) = b , a , inj₁ (c₂ , c₁ , TSP.isym (inda w1 e1) a b eqa)
    h w1 e1 (a , b , inj₂ (c₁ , c₂ , eqa)) = b , a , inj₂ (c₂ , c₁ , TSP.isym (indb w1 e1) a b eqa)



typeSysConds-UNION-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                         (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g
                → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' g h
                → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f h)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb))
      rewrite #INLinj {b} {c} (#⇛!-val-det {_} {g} tt tt c₂ d₁)
      = a , d , inj₁ (c₁ , d₂ , TSP.itrans (inda w1 e1) a c d ea eb)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb)) = ⊥-elim (INLneqINR (⇛!-val-det tt tt c₂ d₁))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb)) = ⊥-elim (INLneqINR (⇛!-val-det tt tt d₁ c₂))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb))
      rewrite #INRinj {b} {c} (#⇛!-val-det {_} {g} tt tt c₂ d₁)
      = a , d , inj₂ (c₁ , d₂ , TSP.itrans (indb w1 e1) a c d ea eb)



typeSysConds-UNION-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi
  rewrite #UNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #UNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
              → UNIONeq (eqInType u w' (eqta0 w' e')) (eqInType u w' (eqtb0 w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a b z)
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extl1 (indb w1 e1) B4 (eqtb0 w1 e1) a b z)

typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-UNION-extl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-UNION-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #UNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-UNION-extl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-UNION-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #UNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extr1 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-UNION-extr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-UNION-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #UNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extr2 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-UNION-extr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)




typeSysConds-UNION-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #UNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-UNION-extrevl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-UNION-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #UNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevl2 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-UNION-extrevl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)




typeSysConds-UNION-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #UNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevr1 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-UNION-extrevr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-UNION-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #UNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #UNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevr2 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-UNION-extrevr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-UNION : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                    (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                    (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                    (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                    → A #⇛ #UNION A1 B1 at w
                    → B #⇛ #UNION A2 B2 at w
                    → (eqt : eqTypes u w A B)
                    → eqInType u w eqt a b
                    → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b
                         → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : eqInType u w1 (eqta w1 e1) v₁ v₂
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : eqInType u w1 (eqtb w1 e1) v₁ v₂
        eqb' = snd (indb w1 e1 (eqtb₁ w1 e1) v₁ v₂) eqb

eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → UNIONeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (eqInType u w'' (eqtb w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-UNION
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-UNION2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                     → A #⇛ #UNION A1 B1 at w
                     → B #⇛ #UNION A2 B2 at w
                     → (eqt : ≡Types u w A B)
                     → (eqi : ≡∈Type u w eqt a b)
                     → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                     → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeUNIONl u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1))
    awextb₁ w1 e1 = ext (eqtb₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeUNIONr u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → UNIONeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) w' a b
                         → UNIONeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) v₁ v₂
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : ≡∈Type u w1 (eqtb w1 e1) v₁ v₂
        eqb' = proj₁ (awextb₁ w1 e1 (eqtb w1 e1) v₁ v₂) eqb

eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → UNIONeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) (≡∈Type u w'' (eqtb w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-UNION2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → UNIONeq (≡∈Type u w'' (eqta w'' x)) (≡∈Type u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-union (u ·ᵤ) w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)





eqInType-⇛-UNION-rev : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                        → A #⇛ #UNION A1 B1 at w
                        → B #⇛ #UNION A2 B2 at w
                        → (eqt : eqTypes u w A B)
                        → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
                        → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b
                         → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) v₁ v₂
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : eqInType u w1 (eqtb₁ w1 e1) v₁ v₂
        eqb' = fst (indb w1 e1 (eqtb₁ w1 e1) v₁ v₂) eqb

eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-UNION-rev
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1





eqInType-⇛-UNION-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                         (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                         → A #⇛ #UNION A1 B1 at w
                         → B #⇛ #UNION A2 B2 at w
                         → (eqt : ≡Types u w A B)
                         → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                         → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
                         → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeUNIONl u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1))
    awextb₁ w1 e1 = ext (eqtb₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeUNIONr u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → UNIONeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) w' a b
                         → UNIONeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) v₁ v₂
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : ≡∈Type u w1 (eqtb₁ w1 e1) v₁ v₂
        eqb' = snd (awextb₁ w1 e1 (eqtb w1 e1) v₁ v₂) eqb

eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (UNIONneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (UNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-UNION-rev2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-UNION-local : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                           → eqInTypeLocal (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → UNIONeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (eqInType u w'' (eqtb w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-UNION u w1 A B A1 A2 B1 B2 a b
                               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
                               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
                               (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
                               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → UNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → UNIONeq (eqInType u w' (eqta w' x₂)) (eqInType u w' (eqtb w' x₂)) w' a b)
        aw'' w' e' (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) x₂ = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
          where
            eqa' : eqInType u w' (eqta w' x₂) v₁ v₂
            eqa' = exta v₁ v₂ w' (⊑-trans· e1 e') x₂ eqa
        aw'' w' e' (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) x₂ = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
          where
            eqb' : eqInType u w' (eqtb w' x₂) v₁ v₂
            eqb' = extb v₁ v₂ w' (⊑-trans· e1 e') x₂ eqb



typeSysConds-UNION : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                     (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                     → TSP {u} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-UNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-UNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-UNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-UNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-tsp→ext indb)
\end{code}
