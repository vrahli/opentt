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

module type_sys_props_tnat {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

TNATneqW : {c : Term} {d : Term} → ¬ TNAT ≡ WT c d
TNATneqW {c} {d} ()

TNATneqM : {c : Term} {d : Term} → ¬ TNAT ≡ MT c d
TNATneqM {c} {d} ()

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

TNATneqNOSEQ : ¬ TNAT ≡ NOSEQ
TNATneqNOSEQ ()

TNATneqTERM : {c : Term} → ¬ TNAT ≡ TERM c
TNATneqTERM {c} ()

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
typeSysConds-TNAT-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2')
              → <Type {u'} eqt' {u} eqt → A #⇛ #TNAT at w' → T1' #⇛ #TNAT at w' → eqTypes u' w' A T2')
          → A #⇛ #TNAT at w → T1 #⇛ #TNAT at w → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih c₁ c₂ = ⊥-elim (TNATneqNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih c₁ c₂ = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih c₁ c₂ = EQTTNAT c₁ y₁
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (TNATneqLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (TNATneqQLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih c₁ c₂ = ⊥-elim (TNATneqFREE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (TNATneqPI (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (TNATneqW (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (TNATneqM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (TNATneqSUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (TNATneqSET (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (TNATneqISECT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih c₁ c₂ = ⊥-elim (TNATneqEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (TNATneqUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih c₁ c₂ = ⊥-elim (TNATneqPURE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih c₁ c₂ = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih c₁ c₂ = ⊥-elim (TNATneqTERM (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih c₁ c₂ = ⊥-elim (TNATneqDUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih c₁ c₂ = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih c₁ c₂ = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih c₁ c₂ = EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (⇛-mon e1 c₁) (⇛-mon e1 c₂)

    concl : (c₁ : A #⇛ #TNAT at w) (c₁ : B #⇛ #TNAT at w) → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (c₁ : A #⇛ #TNAT at w) (c₂ : T1 #⇛ #TNAT at w) → eqTypes u w A T2)
        ind
        eqt



typeSysConds-TNAT-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtL1 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #TNAT at w') (a b : CTerm) → □· w' (λ w'' _ → TNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TNAT-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #TNAT at w') (a b : CTerm) → □· w' (λ w'' _ → TNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-TNAT-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #TNAT at w') (a b : CTerm) → □· w' (λ w'' _ → TNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-TNAT-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #TNAT at w') (a b : CTerm) → □· w' (λ w'' _ → TNATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → □· w (λ w' _ → TNATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-TNAT-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                             → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #TNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → TNATeq w'' a b))
          → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → TNATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b))
        ind
        eqt'


typeSysConds-TNAT-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #TNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → TNATeq w'' a b))
          → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → TNATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b))
        ind
        eqt'



typeSysConds-TNAT-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #TNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → TNATeq w'' a b))
          → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → TNATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b))
        ind
        eqt'


typeSysConds-TNAT-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTTNAT x x₁)
typeSysConds-TNAT-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #TNAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → TNATeq w'' a b))
          → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → TNATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (TNATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (TNATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (TNATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (TNATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (TNATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (TNATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (TNATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (TNATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (TNATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (TNATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (TNATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (TNATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (TNATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → TNATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → TNATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #TNAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → TNATeq w' a b))
        ind
        eqt'


eqInType-⇛-TNAT : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                  → A #⇛ #TNAT at w
                  → B #⇛ #TNAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → □· w (λ w' e → TNATeq w' a b)
eqInType-⇛-TNAT u w A B a b c₁ c₂ eqt ei = typeSysConds-TNAT-extrevl1 u w A B c₁ c₂ B eqt a b ei



eqInType-⇛-TNAT-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #TNAT at w
                       → B #⇛ #TNAT at w
                       → (eqt : eqTypes u w A B)
                       → □· w (λ w' _ → TNATeq w' a b)
                       → eqInType u w eqt a b
eqInType-⇛-TNAT-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-TNAT-extl1 u w A B c₁ c₂ B eqt a b ei



typeSysConds-TNAT-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                          (x : A #⇛ #TNAT at w) (x₁ : B #⇛ #TNAT at w)
                          → eqInTypeLocal {u} (EQTTNAT x x₁)
typeSysConds-TNAT-local u w A B x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : at□· i w' e' z) → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → TNATeq w'' a b))
    aw w1 e1 z at ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
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
