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


module type_sys_props_noenc {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
NOENCneqPURE : ¬ NOENC ≡ PURE
NOENCneqPURE ()

NOENCneqNOSEQ : ¬ NOENC ≡ NOSEQ
NOENCneqNOSEQ ()

NOENCneqTERM : {c : Term} → ¬ NOENC ≡ TERM c
NOENCneqTERM {c} ()

--NOENCneqNAT : ¬ NOENC ≡ NAT
--NOENCneqNAT ()

NOENCneqQNAT : ¬ NOENC ≡ QNAT
NOENCneqQNAT ()

--NOENCneqTNAT : ¬ NOENC ≡ TNAT
--NOENCneqTNAT ()

NOENCneqLT : {c d : Term} → ¬ NOENC ≡ LT c d
NOENCneqLT {c} {d} ()

NOENCneqQLT : {c d : Term} → ¬ NOENC ≡ QLT c d
NOENCneqQLT {c} {d} ()

NOENCneqFREE : ¬ NOENC ≡ FREE
NOENCneqFREE ()

NOENCneqPI : {c : Term} {d : Term} → ¬ NOENC ≡ PI c d
NOENCneqPI {c} {d} ()

NOENCneqW : {c d e : Term} → ¬ NOENC ≡ WT c d e
NOENCneqW {c} {d} {e} ()

NOENCneqM : {c d e : Term} → ¬ NOENC ≡ MT c d e
NOENCneqM {c} {d} {e} ()

NOENCneqSUM : {c : Term} {d : Term} → ¬ NOENC ≡ SUM c d
NOENCneqSUM {c} {d} ()

NOENCneqSET : {c : Term} {d : Term} → ¬ NOENC ≡ SET c d
NOENCneqSET {c} {d} ()

NOENCneqISECT : {c : Term} {d : Term} → ¬ NOENC ≡ ISECT c d
NOENCneqISECT {c} {d} ()

NOENCneqTUNION : {c : Term} {d : Term} → ¬ NOENC ≡ TUNION c d
NOENCneqTUNION {c} {d} ()

NOENCneqUNION : {c : Term} {d : Term} → ¬ NOENC ≡ UNION c d
NOENCneqUNION {c} {d} ()

--NOENCneqQTUNION : {c : Term} {d : Term} → ¬ NOENC ≡ QTUNION c d
--NOENCneqQTUNION {c} {d} ()

NOENCneqEQ : {c d e : Term} → ¬ NOENC ≡ EQ c d e
NOENCneqEQ {c} {d} {e} ()

NOENCneqDUM : {c : Term} → ¬ NOENC ≡ DUM c
NOENCneqDUM {c} ()

NOENCneqFFDEFS : {c d : Term} → ¬ NOENC ≡ FFDEFS c d
NOENCneqFFDEFS {c} {d} ()

NOENCneqSUBSING : {b : Term} → ¬ NOENC ≡ SUBSING b
NOENCneqSUBSING {b} ()

--NOENCneqLIFT : {c : Term} → ¬ NOENC ≡ LIFT c
--NOENCneqLIFT {c} ()

--NOENCneqTSQUASH : {c : Term} → ¬ NOENC ≡ TSQUASH c
--NOENCneqTSQUASH {c} ()

--NOENCneqTTRUNC : {c : Term} → ¬ NOENC ≡ TTRUNC c
--NOENCneqTTRUNC {c} ()

NOENCneqNOWRITE : ¬ NOENC ≡ NOWRITE
NOENCneqNOWRITE ()

NOENCneqNOREAD : ¬ NOENC ≡ NOREAD
NOENCneqNOREAD ()

NOENCneqLOWER : {c : Term} → ¬ NOENC ≡ LOWER c
NOENCneqLOWER {c} ()

NOENCneqSHRINK : {c : Term} → ¬ NOENC ≡ SHRINK c
NOENCneqSHRINK {c} ()

NOENCneqUNIV : {n : ℕ} → ¬ NOENC ≡ UNIV n
NOENCneqUNIV {n} ()


typeSysConds-NOENC-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                            → eqTypes u w B A
typeSysConds-NOENC-tsym u w A B x x₁ = EQTNOENC x₁ x



typeSysConds-NOENC-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                              → eqTypesTrans u w A B
typeSysConds-NOENC-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (c₁ : A #⇛ #NOENC at w') (c₂ : T1' #⇛ #NOENC at w') → eqTypes u' w' A T2')
          → (c₁ : A #⇛ #NOENC at w) (c₂ : T1 #⇛ #NOENC at w) → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (NOENCneqLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NOENCneqPI (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih c₁ c₂ = ⊥-elim (NOENCneqW (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih c₁ c₂ = ⊥-elim (NOENCneqM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NOENCneqSET (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih c₁ c₂ = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih c₁ c₂ = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih c₁ c₂ = EQTNOENC c₁ y₁
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih c₁ c₂ = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih c₁ c₂ = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih c₁ c₂ = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih c₁ c₂ = EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (⇛-mon e1 c₁) (⇛-mon e1 c₂)

    concl : (c₁ : A #⇛ #NOENC at w) (c₁ : B #⇛ #NOENC at w) → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (c₁ : A #⇛ #NOENC at w) (c₂ : T1 #⇛ #NOENC at w) → eqTypes u w A T2)
        ind
        eqt


typeSysConds-NOENC-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                            → eqInTypeSym u {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → NOENCeq f g
                      → NOENCeq g f)
    h w1 e1 (lift (n1 , n2)) = lift (n2 , n1)



typeSysConds-NOENC-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → NOENCeq f g
                      → NOENCeq g h
                      → NOENCeq f h)
    aw w1 e1 (lift (p₁ , p₂)) (lift (q₁ , q₂)) = lift (p₁ , q₂)



typeSysConds-NOENC-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extl1 u w A B x x₁ C eqt' =
  concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NOENC at w') (a b : CTerm) → □· w' (λ w'' _ → NOENCeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOENC-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NOENC at w') (a b : CTerm) → □· w' (λ w'' _ → NOENCeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOENC-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NOENC at w') (a b : CTerm) → □· w' (λ w'' _ → NOENCeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOENC-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NOENC at w') (a b : CTerm) → □· w' (λ w'' _ → NOENCeq a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → □· w (λ w' _ → NOENCeq a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOENC-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NOENC at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NOENCeq a b))
          → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NOENCeq a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NOENCeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NOENCeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b))
        ind
        eqt'



typeSysConds-NOENC-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NOENC at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NOENCeq a b))
          → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NOENCeq a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NOENCeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NOENCeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b))
        ind
        eqt'



typeSysConds-NOENC-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NOENC at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NOENCeq a b))
          → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NOENCeq a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NOENCeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NOENCeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b))
        ind
        eqt'



typeSysConds-NOENC-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOENC x x₁)
typeSysConds-NOENC-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NOENC at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NOENCeq a b))
          → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NOENCeq a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqQNAT (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NOENCneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NOENCneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 y y₁ eqta eqtb eqtc exta extb extc) ih comp a b eqi = ⊥-elim (NOENCneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NOENCneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NOENCneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NOENCneqQTUNION (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTSQUASH (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOWRITE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOREAD (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NOENCneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NOENCneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NOENCneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NOENCneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NOENCneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NOENCneqUNIV (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NOENCneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NOENCeq a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NOENCeq a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NOENC at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NOENCeq a b))
        ind
        eqt'




eqInType-⇛-NOENC : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #NOENC at w
                      → B #⇛ #NOENC at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → NOENCeq a b)
eqInType-⇛-NOENC u w A B a b c₁ c₂ eqt ei = typeSysConds-NOENC-extrevl1 u w A B c₁ c₂ B eqt a b ei




eqInType-⇛-NOENC2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #NOENC at w
                       → B #⇛ #NOENC at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → NOENCeq a b)
eqInType-⇛-NOENC2 u w A B a b c₁ c₂ eqt ei = typeSysConds-NOENC-extrevl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei




eqInType-⇛-NOENC-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #NOENC at w
                          → B #⇛ #NOENC at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → NOENCeq a b)
                          → eqInType u w eqt a b
eqInType-⇛-NOENC-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-NOENC-extl1 u w A B c₁ c₂ B eqt a b ei



eqInType-⇛-NOENC-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #NOENC at w
                           → B #⇛ #NOENC at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → NOENCeq a b)
                           → ≡∈Type u w eqt a b
eqInType-⇛-NOENC-rev2 u w A B a b c₁ c₂ eqt ei = typeSysConds-NOENC-extl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei



typeSysConds-NOENC-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                             → eqInTypeLocal (EQTNOENC x x₁)
typeSysConds-NOENC-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → NOENCeq a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → NOENCeq a b)
        aw' = eqInType-⇛-NOENC u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → NOENCeq a b
                                → (x₂ : w ⊑· w') → NOENCeq a b)
        aw'' w' e' p x₂ = p



typeSysConds-NOENC : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #NOENC at w) (x₁ : B #⇛ #NOENC at w)
                       → TSP {u} (EQTNOENC x x₁)
typeSysConds-NOENC u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-NOENC-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NOENC-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTNOENC x x₁)
    isym = typeSysConds-NOENC-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNOENC x x₁)
    itrans = typeSysConds-NOENC-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextl1 = typeSysConds-NOENC-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextl2 = typeSysConds-NOENC-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextr1 = typeSysConds-NOENC-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextr2 = typeSysConds-NOENC-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextrl1 = typeSysConds-NOENC-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextrl2 = typeSysConds-NOENC-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextrr1 = typeSysConds-NOENC-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOENC x x₁)
    iextrr2 = typeSysConds-NOENC-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTNOENC x x₁)
    local = typeSysConds-NOENC-local u w A B x x₁
\end{code}
