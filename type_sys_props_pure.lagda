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


module type_sys_props_pure {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
PUREneqTERM : {c : Term} → ¬ PURE ≡ TERM c
PUREneqTERM {c} ()

PUREneqNOSEQ : ¬ PURE ≡ NOSEQ
PUREneqNOSEQ ()

PUREneqNAT : ¬ PURE ≡ NAT
PUREneqNAT ()

PUREneqQNAT : ¬ PURE ≡ QNAT
PUREneqQNAT ()

PUREneqTNAT : ¬ PURE ≡ TNAT
PUREneqTNAT ()

PUREneqLT : {c d : Term} → ¬ PURE ≡ LT c d
PUREneqLT {c} {d} ()

PUREneqQLT : {c d : Term} → ¬ PURE ≡ QLT c d
PUREneqQLT {c} {d} ()

PUREneqFREE : ¬ PURE ≡ FREE
PUREneqFREE ()

PUREneqPI : {c : Term} {d : Term} → ¬ PURE ≡ PI c d
PUREneqPI {c} {d} ()

PUREneqW : {c : Term} {d : Term} → ¬ PURE ≡ WT c d
PUREneqW {c} {d} ()

PUREneqM : {c : Term} {d : Term} → ¬ PURE ≡ MT c d
PUREneqM {c} {d} ()

PUREneqSUM : {c : Term} {d : Term} → ¬ PURE ≡ SUM c d
PUREneqSUM {c} {d} ()

PUREneqSET : {c : Term} {d : Term} → ¬ PURE ≡ SET c d
PUREneqSET {c} {d} ()

PUREneqISECT : {c : Term} {d : Term} → ¬ PURE ≡ ISECT c d
PUREneqISECT {c} {d} ()

PUREneqTUNION : {c : Term} {d : Term} → ¬ PURE ≡ TUNION c d
PUREneqTUNION {c} {d} ()

PUREneqUNION : {c : Term} {d : Term} → ¬ PURE ≡ UNION c d
PUREneqUNION {c} {d} ()

--PUREneqQTUNION : {c : Term} {d : Term} → ¬ PURE ≡ QTUNION c d
--PUREneqQTUNION {c} {d} ()

PUREneqEQ : {c d e : Term} → ¬ PURE ≡ EQ c d e
PUREneqEQ {c} {d} {e} ()

PUREneqDUM : {c : Term} → ¬ PURE ≡ DUM c
PUREneqDUM {c} ()

PUREneqFFDEFS : {c d : Term} → ¬ PURE ≡ FFDEFS c d
PUREneqFFDEFS {c} {d} ()

PUREneqSUBSING : {b : Term} → ¬ PURE ≡ SUBSING b
PUREneqSUBSING {b} ()

PUREneqLIFT : {c : Term} → ¬ PURE ≡ LIFT c
PUREneqLIFT {c} ()

PUREneqTSQUASH : {c : Term} → ¬ PURE ≡ TSQUASH c
PUREneqTSQUASH {c} ()

--PUREneqTTRUNC : {c : Term} → ¬ PURE ≡ TTRUNC c
--PUREneqTTRUNC {c} ()

PUREneqNOWRITE : {c : Term} → ¬ PURE ≡ NOWRITE c
PUREneqNOWRITE {c} ()

PUREneqNOREAD : {c : Term} → ¬ PURE ≡ NOREAD c
PUREneqNOREAD {c} ()

PUREneqLOWER : {c : Term} → ¬ PURE ≡ LOWER c
PUREneqLOWER {c} ()

PUREneqSHRINK : {c : Term} → ¬ PURE ≡ SHRINK c
PUREneqSHRINK {c} ()

PUREneqUNIV : {n : ℕ} → ¬ PURE ≡ UNIV n
PUREneqUNIV {n} ()


typeSysConds-PURE-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                            → eqTypes u w B A
typeSysConds-PURE-tsym u w A B x x₁ = EQTPURE x₁ x



typeSysConds-PURE-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                              → eqTypesTrans u w A B
typeSysConds-PURE-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (c₁ : A #⇛ #PURE at w') (c₂ : T1' #⇛ #PURE at w') → eqTypes u' w' A T2')
          → (c₁ : A #⇛ #PURE at w) (c₂ : T1 #⇛ #PURE at w) → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih c₁ c₂ = ⊥-elim (PUREneqNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih c₁ c₂ = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih c₁ c₂ = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (PUREneqLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (PUREneqQLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih c₁ c₂ = ⊥-elim (PUREneqFREE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (PUREneqPI (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (PUREneqW (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (PUREneqM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (PUREneqSUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (PUREneqSET (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (PUREneqISECT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih c₁ c₂ = ⊥-elim (PUREneqEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (PUREneqUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih c₁ c₂ = ⊥-elim (PUREneqDUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih c₁ c₂ = EQTPURE c₁ y₁
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih c₁ c₂ = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih c₁ c₂ = ⊥-elim (PUREneqTERM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih c₁ c₂ = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih c₁ c₂ = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih c₁ c₂ = EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (⇛-mon e1 c₁) (⇛-mon e1 c₂)

    concl : (c₁ : A #⇛ #PURE at w) (c₁ : B #⇛ #PURE at w) → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (c₁ : A #⇛ #PURE at w) (c₂ : T1 #⇛ #PURE at w) → eqTypes u w A T2)
        ind
        eqt


typeSysConds-PURE-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                            → eqInTypeSym u {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → PUREeq f g
                       → PUREeq g f)
    h w1 e1 (lift (n1 , n2)) = lift (n2 , n1)



typeSysConds-PURE-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → PUREeq f g
                      → PUREeq g h
                      → PUREeq f h)
    aw w1 e1 (lift (p₁ , p₂)) (lift (q₁ , q₂)) = lift (p₁ , q₂)



typeSysConds-PURE-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extl1 u w A B x x₁ C eqt' =
  concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #PURE at w') (a b : CTerm) → □· w' (λ w'' _ → PUREeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-PURE-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #PURE at w') (a b : CTerm) → □· w' (λ w'' _ → PUREeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-PURE-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #PURE at w') (a b : CTerm) → □· w' (λ w'' _ → PUREeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-PURE-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #PURE at w') (a b : CTerm) → □· w' (λ w'' _ → PUREeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → □· w (λ w' _ → PUREeq a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-PURE-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #PURE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → PUREeq a b))
          → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → PUREeq a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → PUREeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → PUREeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b))
        ind
        eqt'



typeSysConds-PURE-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #PURE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → PUREeq a b))
          → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → PUREeq a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → PUREeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → PUREeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b))
        ind
        eqt'



typeSysConds-PURE-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #PURE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → PUREeq a b))
          → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → PUREeq a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → PUREeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → PUREeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b))
        ind
        eqt'



typeSysConds-PURE-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTPURE x x₁)
typeSysConds-PURE-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #PURE at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → PUREeq a b))
          → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → PUREeq a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (PUREneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (PUREneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (PUREneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (PUREneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (PUREneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (PUREneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (PUREneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (PUREneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (PUREneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (PUREneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (PUREneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (PUREneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → PUREeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → PUREeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #PURE at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → PUREeq a b))
        ind
        eqt'



eqInType-⇛-PURE : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #PURE at w
                      → B #⇛ #PURE at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → PUREeq a b)
eqInType-⇛-PURE u w A B a b c₁ c₂ eqt ei = typeSysConds-PURE-extrevl1 u w A B c₁ c₂ B eqt a b ei



eqInType-⇛-PURE2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #PURE at w
                       → B #⇛ #PURE at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → PUREeq a b)
eqInType-⇛-PURE2 u w A B a b c₁ c₂ eqt ei = typeSysConds-PURE-extrevl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei



eqInType-⇛-PURE-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #PURE at w
                          → B #⇛ #PURE at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → PUREeq a b)
                          → eqInType u w eqt a b
eqInType-⇛-PURE-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-PURE-extl1 u w A B c₁ c₂ B eqt a b ei



eqInType-⇛-PURE-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #PURE at w
                           → B #⇛ #PURE at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → PUREeq a b)
                           → ≡∈Type u w eqt a b
eqInType-⇛-PURE-rev2 u w A B a b c₁ c₂ eqt ei = typeSysConds-PURE-extl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei


typeSysConds-PURE-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                             → eqInTypeLocal (EQTPURE x x₁)
typeSysConds-PURE-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → PUREeq a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → PUREeq a b)
        aw' = eqInType-⇛-PURE u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → PUREeq a b
                                → (x₂ : w ⊑· w') → PUREeq a b)
        aw'' w' e' p x₂ = p



typeSysConds-PURE : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #PURE at w) (x₁ : B #⇛ #PURE at w)
                       → TSP {u} (EQTPURE x x₁)
typeSysConds-PURE u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-PURE-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-PURE-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTPURE x x₁)
    isym = typeSysConds-PURE-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTPURE x x₁)
    itrans = typeSysConds-PURE-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextl1 = typeSysConds-PURE-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextl2 = typeSysConds-PURE-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextr1 = typeSysConds-PURE-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextr2 = typeSysConds-PURE-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrl1 = typeSysConds-PURE-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrl2 = typeSysConds-PURE-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrr1 = typeSysConds-PURE-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTPURE x x₁)
    iextrr2 = typeSysConds-PURE-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTPURE x x₁)
    local = typeSysConds-PURE-local u w A B x x₁
\end{code}
