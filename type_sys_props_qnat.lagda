\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


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
open import newChoice
open import mod
open import encode

module type_sys_props_qnat {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

-- open import Function.Bundles
-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
\end{code}



\begin{code}[hide]
-- QNAT
--QNATneqNAT : ¬ QNAT ≡ NAT
--QNATneqNAT ()

--QNATneqTNAT : ¬ QNAT ≡ TNAT
--QNATneqTNAT ()

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

QNATneqW : {c d e : Term} → ¬ QNAT ≡ WT c d e
QNATneqW {c} {d} {e} ()

QNATneqM : {c d e : Term} → ¬ QNAT ≡ MT c d e
QNATneqM {c} {d} {e} ()

QNATneqSET : {c : Term} {d : Term} → ¬ QNAT ≡ SET c d
QNATneqSET {c} {d} ()

QNATneqTUNION : {c : Term} {d : Term} → ¬ QNAT ≡ TUNION c d
QNATneqTUNION {c} {d} ()

QNATneqISECT : {c : Term} {d : Term} → ¬ QNAT ≡ ISECT c d
QNATneqISECT {c} {d} ()

QNATneqUNION : {c : Term} {d : Term} → ¬ QNAT ≡ UNION c d
QNATneqUNION {c} {d} ()

--QNATneqQTUNION : {c : Term} {d : Term} → ¬ QNAT ≡ QTUNION c d
--QNATneqQTUNION {c} {d} ()

QNATneqEQ : {c d e : Term} → ¬ QNAT ≡ EQ c d e
QNATneqEQ {c} {d} {e} ()

--QNATneqTSQUASH : {c : Term} → ¬ QNAT ≡ TSQUASH c
--QNATneqTSQUASH {c} ()

--QNATneqTTRUNC : {c : Term} → ¬ QNAT ≡ TTRUNC c
--QNATneqTTRUNC {c} ()

QNATneqNOWRITE : ¬ QNAT ≡ NOWRITE
QNATneqNOWRITE ()

QNATneqNOREAD : ¬ QNAT ≡ NOREAD
QNATneqNOREAD ()

QNATneqSUBSING : {c : Term} → ¬ QNAT ≡ SUBSING c
QNATneqSUBSING {c} ()

QNATneqPURE : ¬ QNAT ≡ PURE
QNATneqPURE ()

QNATneqNOSEQ : ¬ QNAT ≡ NOSEQ
QNATneqNOSEQ ()

QNATneqNOENC : ¬ QNAT ≡ NOENC
QNATneqNOENC ()

QNATneqTERM : {c : Term} → ¬ QNAT ≡ TERM c
QNATneqTERM {c} ()

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
typeSysConds-QNAT-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (c₁ : A #⇛ #QNAT at w') (c₂ : T1' #⇛ #QNAT at w') → eqTypes u' w' A T2')
          → (c₁ : A #⇛ #QNAT at w) (c₂ : T1 #⇛ #QNAT at w) → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih c₁ c₂ = ⊥-elim (QNATneqNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih c₁ c₂ = EQTQNAT c₁ y₁
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih c₁ c₂ = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (QNATneqLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (QNATneqQLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih c₁ c₂ = ⊥-elim (QNATneqFREE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (QNATneqPI (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih c₁ c₂ = ⊥-elim (QNATneqW (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih c₁ c₂ = ⊥-elim (QNATneqM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (QNATneqSUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (QNATneqSET (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (QNATneqISECT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih c₁ c₂ = ⊥-elim (QNATneqEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (QNATneqUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih c₁ c₂ = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih c₁ c₂ = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih c₁ c₂ = ⊥-elim (QNATneqDUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih c₁ c₂ = ⊥-elim (QNATneqPURE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih c₁ c₂ = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih c₁ c₂ = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih c₁ c₂ = ⊥-elim (QNATneqTERM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih c₁ c₂ = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih c₁ c₂ = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih c₁ c₂ = EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (⇛-mon e1 c₁) (⇛-mon e1 c₂)

    concl : (c₁ : A #⇛ #QNAT at w) (c₁ : B #⇛ #QNAT at w) → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (c₁ : A #⇛ #QNAT at w) (c₂ : T1 #⇛ #QNAT at w) → eqTypes u w A T2)
        ind
        eqt



typeSysConds-QNAT-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtL1 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extl1 u w A B x x₁ C eqt' =
  concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #QNAT at w') (a b : CTerm) → □· w' (λ w'' _ → QNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QNAT-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #QNAT at w') (a b : CTerm) → □· w' (λ w'' _ → QNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QNAT-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #QNAT at w') (a b : CTerm) → □· w' (λ w'' _ → QNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QNAT-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #QNAT at w') (a b : CTerm) → □· w' (λ w'' _ → QNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → □· w (λ w' _ → QNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-QNAT-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #QNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → QNATeq w'' a b))
          → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → QNATeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → QNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → QNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b))
        ind
        eqt'



typeSysConds-QNAT-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #QNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → QNATeq w'' a b))
          → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → QNATeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → QNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → QNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b))
        ind
        eqt'



typeSysConds-QNAT-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #QNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → QNATeq w'' a b))
          → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → QNATeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → QNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → QNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b))
        ind
        eqt'



typeSysConds-QNAT-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTQNAT x x₁)
typeSysConds-QNAT-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #QNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → QNATeq w'' a b))
          → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → QNATeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = eqi
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (QNATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (QNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (QNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (QNATneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (QNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (QNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (QNATneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (QNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (QNATneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (QNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → QNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → QNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #QNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → QNATeq w' a b))
        ind
        eqt'


eqInType-⇛-QNAT : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                  → A #⇛ #QNAT at w
                  → B #⇛ #QNAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → □· w (λ w' e → #weakMonEq w' a b)
eqInType-⇛-QNAT u w A B a b c₁ c₂ eqt ei = typeSysConds-QNAT-extrevl1 u w A B c₁ c₂ B eqt a b ei


eqInType-⇛-QNAT-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #QNAT at w
                       → B #⇛ #QNAT at w
                       → (eqt : eqTypes u w A B)
                       → □· w (λ w' _ → #weakMonEq w' a b)
                       → eqInType u w eqt a b
eqInType-⇛-QNAT-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-QNAT-extl1 u w A B c₁ c₂ B eqt a b ei


typeSysConds-QNAT-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                          (x : A #⇛ #QNAT at w) (x₁ : B #⇛ #QNAT at w)
                          → eqInTypeLocal {u} (EQTQNAT x x₁)
typeSysConds-QNAT-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
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
