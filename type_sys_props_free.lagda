\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

--open import bar
--module type_sys_props_free (bar : Bar) where

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


module type_sys_props_free {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
\end{code}



\begin{code}[hide]
--FREEneqNAT : ¬ FREE ≡ NAT
--FREEneqNAT ()

FREEneqQNAT : ¬ FREE ≡ QNAT
FREEneqQNAT ()

--FREEneqTNAT : ¬ FREE ≡ TNAT
--FREEneqTNAT ()

FREEneqLT : {c d : Term} → ¬ FREE ≡ LT c d
FREEneqLT {c} {d} ()

FREEneqQLT : {c d : Term} → ¬ FREE ≡ QLT c d
FREEneqQLT {c} {d} ()

FREEneqPI : {c : Term} {d : Term} → ¬ FREE ≡ PI c d
FREEneqPI {c} {d} ()

FREEneqW : {c d e : Term} → ¬ FREE ≡ WT c d e
FREEneqW {c} {d} {e} ()

FREEneqM : {c d e : Term} → ¬ FREE ≡ MT c d e
FREEneqM {c} {d} {e} ()

FREEneqSUM : {c : Term} {d : Term} → ¬ FREE ≡ SUM c d
FREEneqSUM {c} {d} ()

FREEneqSET : {c : Term} {d : Term} → ¬ FREE ≡ SET c d
FREEneqSET {c} {d} ()

FREEneqTUNION : {c : Term} {d : Term} → ¬ FREE ≡ TUNION c d
FREEneqTUNION {c} {d} ()

FREEneqUNION : {c : Term} {d : Term} → ¬ FREE ≡ UNION c d
FREEneqUNION {c} {d} ()

FREEneqISECT : {c : Term} {d : Term} → ¬ FREE ≡ ISECT c d
FREEneqISECT {c} {d} ()

--FREEneqQTUNION : {c : Term} {d : Term} → ¬ FREE ≡ QTUNION c d
--FREEneqQTUNION {c} {d} ()

FREEneqEQ : {c d e : Term} → ¬ FREE ≡ EQ c d e
FREEneqEQ {c} {d} {e} ()

--FREEneqTSQUASH : {c : Term} → ¬ FREE ≡ TSQUASH c
--FREEneqTSQUASH {c} ()

--FREEneqTTRUNC : {c : Term} → ¬ FREE ≡ TTRUNC c
--FREEneqTTRUNC {c} ()

FREEneqNOWRITE : ¬ FREE ≡ NOWRITE
FREEneqNOWRITE ()

FREEneqNOREAD : ¬ FREE ≡ NOREAD
FREEneqNOREAD ()

FREEneqSUBSING : {c : Term} → ¬ FREE ≡ SUBSING c
FREEneqSUBSING {c} ()

FREEneqPURE : ¬ FREE ≡ PURE
FREEneqPURE ()

FREEneqNOSEQ : ¬ FREE ≡ NOSEQ
FREEneqNOSEQ ()

FREEneqNOENC : ¬ FREE ≡ NOENC
FREEneqNOENC ()

FREEneqTERM : {c : Term} → ¬ FREE ≡ TERM c
FREEneqTERM {c} ()

FREEneqLIFT : {c : Term} → ¬ FREE ≡ LIFT c
FREEneqLIFT {c} ()

FREEneqDUM : {c : Term} → ¬ FREE ≡ DUM c
FREEneqDUM {c} ()

FREEneqFFDEFS : {c d : Term} → ¬ FREE ≡ FFDEFS c d
FREEneqFFDEFS {c} {d} ()

FREEneqLOWER : {c : Term} → ¬ FREE ≡ LOWER c
FREEneqLOWER {c} ()

FREEneqSHRINK : {c : Term} → ¬ FREE ≡ SHRINK c
FREEneqSHRINK {c} ()

FREEneqUNIV : {n : ℕ} → ¬ FREE ≡ UNIV n
FREEneqUNIV {n} ()



typeSysConds-FREE-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                           (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                           → eqTypesTrans u w A B
typeSysConds-FREE-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (c₁ : A #⇛ #FREE at w') (c₂ : T1' #⇛ #FREE at w') → eqTypes u' w' A T2')
          → (c₁ : A #⇛ #FREE at w) (c₂ : T1 #⇛ #FREE at w) → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih c₁ c₂ = ⊥-elim (FREEneqNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih c₁ c₂ = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih c₁ c₂ = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (FREEneqLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (FREEneqQLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih c₁ c₂ = EQTFREE c₁ y₁
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (FREEneqPI (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih c₁ c₂ = ⊥-elim (FREEneqW (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih c₁ c₂ = ⊥-elim (FREEneqM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (FREEneqSUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (FREEneqSET (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (FREEneqISECT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih c₁ c₂ = ⊥-elim (FREEneqEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (FREEneqUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih c₁ c₂ = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih c₁ c₂ = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih c₁ c₂ = ⊥-elim (FREEneqDUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih c₁ c₂ = ⊥-elim (FREEneqPURE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih c₁ c₂ = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih c₁ c₂ = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih c₁ c₂ = ⊥-elim (FREEneqTERM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih c₁ c₂ = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih c₁ c₂ = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih c₁ c₂ = EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (⇛-mon e1 c₁) (⇛-mon e1 c₂)

    concl : (c₁ : A #⇛ #FREE at w) (c₁ : B #⇛ #FREE at w) → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (c₁ : A #⇛ #FREE at w) (c₂ : T1 #⇛ #FREE at w) → eqTypes u w A T2)
        ind
        eqt


typeSysConds-FREE-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                         → eqInTypeExtL1 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extl1 u w A B x x₁ C eqt' =
  concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #FREE at w') (a b : CTerm) → □· w' (λ w'' _ → FREEeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-FREE-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #FREE at w') (a b : CTerm) → □· w' (λ w'' _ → FREEeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-FREE-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #FREE at w') (a b : CTerm) → □· w' (λ w'' _ → FREEeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-FREE-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #FREE at w') (a b : CTerm) → □· w' (λ w'' _ → FREEeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → □· w (λ w' _ → FREEeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-FREE-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                            → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #FREE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → FREEeq w'' a b))
          → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → FREEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → FREEeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → FREEeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b))
        ind
        eqt'


typeSysConds-FREE-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #FREE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → FREEeq w'' a b))
          → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → FREEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → FREEeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → FREEeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b))
        ind
        eqt'


typeSysConds-FREE-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #FREE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → FREEeq w'' a b))
          → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → FREEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → FREEeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → FREEeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b))
        ind
        eqt'


typeSysConds-FREE-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTFREE x x₁)
typeSysConds-FREE-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #FREE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → FREEeq w'' a b))
          → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → FREEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (FREEneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (FREEneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (FREEneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (FREEneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (FREEneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (FREEneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = ⊥-elim (FREEneqNOENC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (FREEneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (FREEneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (FREEneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → FREEeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → FREEeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #FREE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → FREEeq w' a b))
        ind
        eqt'


eqInType-⇛-FREE : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                   → A #⇛ #FREE at w
                   → B #⇛ #FREE at w
                   → (eqt : eqTypes u w A B)
                   → eqInType u w eqt a b
                   → □· w (λ w' e → #⇛to-same-CS w' a b)
eqInType-⇛-FREE u w A B a b c₁ c₂ eqt ei = typeSysConds-FREE-extrevl1 u w A B c₁ c₂ B eqt a b ei


eqInType-⇛-FREE-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #FREE at w
                       → B #⇛ #FREE at w
                       → (eqt : eqTypes u w A B)
                       → □· w (λ w' e → #⇛to-same-CS w' a b)
                       → eqInType u w eqt a b
eqInType-⇛-FREE-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-FREE-extl1 u w A B c₁ c₂ B eqt a b ei


typeSysConds-FREE-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                         → eqInTypeLocal {u} (EQTFREE x x₁)
typeSysConds-FREE-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--} → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → #⇛to-same-CS w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
      where
        aw' : □· w1 (λ w' e → #⇛to-same-CS w' a b)
        aw' = eqInType-⇛-FREE u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-FREE : (u : univs) (w : 𝕎·) (A B : CTerm)
                   (x : A #⇛ #FREE at w) (x₁ : B #⇛ #FREE at w)
                   → TSP {u} (EQTFREE x x₁)
typeSysConds-FREE u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTFREE x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-FREE-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTFREE x x₁)
    isym a b eqi = □·-⇛to-same-CS-sym eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTFREE x x₁)
    itrans a b c eqi₁ eqi₂ = □·-⇛to-same-CS-trans eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTFREE x x₁)
    iextl1 = typeSysConds-FREE-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTFREE x x₁)
    iextl2 = typeSysConds-FREE-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTFREE x x₁)
    iextr1 = typeSysConds-FREE-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTFREE x x₁)
    iextr2 = typeSysConds-FREE-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTFREE x x₁)
    iextrl1 = typeSysConds-FREE-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTFREE x x₁)
    iextrl2 = typeSysConds-FREE-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTFREE x x₁)
    iextrr1 = typeSysConds-FREE-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTFREE x x₁)
    iextrr2 = typeSysConds-FREE-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTFREE x x₁)
    local = typeSysConds-FREE-local u w A B x x₁
\end{code}
