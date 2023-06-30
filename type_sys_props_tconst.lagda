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


module type_sys_props_tconst {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; <TypeNOWRITE to <TypeNOWRITE₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
NOWRITEneqNAT : {a : Term} → ¬ (NOWRITE a) ≡ NAT
NOWRITEneqNAT {a} ()

NOWRITEneqQNAT : {a : Term} → ¬ (NOWRITE a) ≡ QNAT
NOWRITEneqQNAT {a} ()

NOWRITEneqTNAT : {a : Term} → ¬ (NOWRITE a) ≡ TNAT
NOWRITEneqTNAT {a} ()

NOWRITEneqLT : {a : Term} {c d : Term} → ¬ (NOWRITE a) ≡ LT c d
NOWRITEneqLT {a} {c} {d} ()

NOWRITEneqQLT : {a : Term} {c d : Term} → ¬ (NOWRITE a) ≡ QLT c d
NOWRITEneqQLT {a} {c} {d} ()

NOWRITEneqFREE : {a : Term} → ¬ (NOWRITE a) ≡ FREE
NOWRITEneqFREE {a} ()

NOWRITEneqPI : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ PI c d
NOWRITEneqPI {a} {c} {d} ()

NOWRITEneqW : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ WT c d
NOWRITEneqW {a} {c} {d} ()

NOWRITEneqM : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ MT c d
NOWRITEneqM {a} {c} {d} ()

NOWRITEneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ SUM c d
NOWRITEneqSUM {a} {c} {d} ()

NOWRITEneqSET : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ SET c d
NOWRITEneqSET {a} {c} {d} ()

NOWRITEneqISECT : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ ISECT c d
NOWRITEneqISECT {a} {c} {d} ()

NOWRITEneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ TUNION c d
NOWRITEneqTUNION {a} {c} {d} ()

NOWRITEneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ UNION c d
NOWRITEneqUNION {a} {c} {d} ()

--NOWRITEneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (NOWRITE a) ≡ QTUNION c d
--NOWRITEneqQTUNION {a} {c} {d} ()

NOWRITEneqEQ : {a : Term} {c d e : Term} → ¬ (NOWRITE a) ≡ EQ c d e
NOWRITEneqEQ {a} {c} {d} {e} ()

NOWRITEneqDUM : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ DUM c
NOWRITEneqDUM {a} {c} ()

NOWRITEneqFFDEFS : {a : Term} {c d : Term} → ¬ (NOWRITE a) ≡ FFDEFS c d
NOWRITEneqFFDEFS {a} {c} {d} ()

NOWRITEneqLIFT : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ LIFT c
NOWRITEneqLIFT {a} {c} ()

NOWRITEneqTSQUASH : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ TSQUASH c
NOWRITEneqTSQUASH {a} {c} ()

--NOWRITEneqTTRUNC : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ TTRUNC c
--NOWRITEneqTTRUNC {a} {c} ()

NOWRITEneqSUBSING : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ SUBSING c
NOWRITEneqSUBSING {a} {c} ()

NOWRITEneqPURE : {a : Term} → ¬ (NOWRITE a) ≡ PURE
NOWRITEneqPURE {a} ()

NOWRITEneqNOSEQ : {a : Term} → ¬ (NOWRITE a) ≡ NOSEQ
NOWRITEneqNOSEQ {a} ()

NOWRITEneqTERM : {a c : Term} → ¬ (NOWRITE a) ≡ TERM c
NOWRITEneqTERM {a} {c} ()

NOWRITEneqLOWER : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ LOWER c
NOWRITEneqLOWER {a} {c} ()

NOWRITEneqSHRINK : {a : Term} {c : Term} → ¬ (NOWRITE a) ≡ SHRINK c
NOWRITEneqSHRINK {a} {c} ()

NOWRITEneqUNIV : {a : Term} {n : ℕ} → ¬ (NOWRITE a) ≡ UNIV n
NOWRITEneqUNIV {a} {n} ()


typeSysConds-NOWRITE-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-NOWRITE-tsym u w A B A1 B1 x x₁ eqta exta inda =
  EQTNOWRITE B1 A1 x₁ x syma exta'
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes u w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) B1 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) B1 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1


typeSysConds-NOWRITE-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
typeSysConds-NOWRITE-ttrans u w A B A1 B1 x x₁ eqta exta inda C eqt = concl x x₁ eqta exta inda
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #NOWRITE A1 at w' → T1' #⇛ #NOWRITE B1 at w'
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → eqTypes u' w' A T2')
          → A #⇛ #NOWRITE A1 at w → T1 #⇛ #NOWRITE B1 at w
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda
      = EQTNOWRITE A1 A4 x y₁ eqa exta'
      where
        eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A4)
        eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (→≡eqTypes (#NOWRITEinj {A3} {B1} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqtA w1 e1))

        exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
        exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) A4 (eqa w' e2) a b ei2
          where
            ei1 : eqInType u w' (eqta w' e1) a b
            ei1 = TSP.extrevl1 (inda w' e1) A4 (eqa w' e1) a b ei

            ei2 : eqInType u w' (eqta w' e2) a b
            ei2 = exta a b w' e1 e2 ei1
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ eqta exta inda =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' inda)

    concl : (c₁ : A #⇛ #NOWRITE A1 at w) (c₁ : B #⇛ #NOWRITE B1 at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #NOWRITE A1 at w) (c₂ : T1 #⇛ #NOWRITE B1 at w)
           → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
           → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
           → eqTypes u w A T2)
        ind
        eqt


typeSysConds-NOWRITE-isym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-isym u w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g
                       → NOWRITEeq (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 p = NOWRITEeq-sym (TSP.isym (inda w1 e1)) p



typeSysConds-NOWRITE-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-itrans u w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' f g
                      → NOWRITEeq (eqInType u w' (eqta w' e)) w' g h
                      → NOWRITEeq (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 p₁ p₂ = NOWRITEeq-trans (TSP.itrans (inda w1 e1)) p₁ p₂



typeSysConds-NOWRITE-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extl1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #NOWRITE A1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #NOWRITE A1 at w → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta exta inda x f g eqi = {!!}
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A3} {A1} (#⇛-val-det {_} {T1} tt tt y x)) =
          NOWRITEeq-ext-eq
            {eqInType u w1 (eqta w1 e1)} {eqInType u w1 (eqtA w1 e1)} {w1} {f} {g}
            (TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : A #⇛ #NOWRITE A1 at w) (a b : CTerm)
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #NOWRITE A1 at w) (a b : CTerm)
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-NOWRITE-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extl2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #NOWRITE A1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #NOWRITE A1 at w
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      --
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A4} {A1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
          NOWRITEeq-ext-eq (TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : A #⇛ #NOWRITE A1 at w)
            (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          →  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #NOWRITE A1 at w)
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOWRITE-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extr1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #NOWRITE B1 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #NOWRITE B1 at w
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A4} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x₁)) =
          NOWRITEeq-ext-eq (TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : B #⇛ #NOWRITE B1 at w)
            (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #NOWRITE B1 at w)
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOWRITE-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extr2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #NOWRITE B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #NOWRITE B1 at w
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A3} {B1} (#⇛-val-det {_} {T1} tt tt y x₁)) =
          NOWRITEeq-ext-eq (TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : B #⇛ #NOWRITE B1 at w)
            (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #NOWRITE B1 at w)
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOWRITE-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #NOWRITE A1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #NOWRITE A1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A3} {A1} (#⇛-val-det {_} {T1} tt tt y x)) =
          NOWRITEeq-ext-eq (TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq (eqInType u w'' (eqta w'' x)) w'' f g))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (irr-tconst u w A1 B1 eqta exta f g w1 e1)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : A #⇛ #NOWRITE A1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #NOWRITE A1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



typeSysConds-NOWRITE-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #NOWRITE A1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #NOWRITE A1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A4} {A1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
          NOWRITEeq-ext-eq (TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq (eqInType u w'' (eqta w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : A #⇛ #NOWRITE A1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #NOWRITE A1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



typeSysConds-NOWRITE-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #NOWRITE B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #NOWRITE B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A4} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x₁)) =
          NOWRITEeq-ext-eq (TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq (eqInType u w'' (eqta w'' x)) w'' f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : B #⇛ #NOWRITE B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #NOWRITE B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



typeSysConds-NOWRITE-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #NOWRITE B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #NOWRITE B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqtA w' e')) w' f g
                            → NOWRITEeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#NOWRITEinj {A3} {B1} (#⇛-val-det {_} {T1} tt tt y x₁)) =
          NOWRITEeq-ext-eq (TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq (eqInType u w'' (eqta w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : B #⇛ #NOWRITE B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #NOWRITE B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'




eqInType-⇛-NOWRITE : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A #⇛ #NOWRITE A1 at w
                      → B #⇛ #NOWRITE B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
eqInType-⇛-NOWRITE u w A B A1 B1 a b eqta exta inda c₁ c₂ eqt eqi = concl eqta exta inda c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (inda₁ :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → T1' #⇛ #NOWRITE A1 at w' → T2' #⇛ #NOWRITE B1 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → T1 #⇛ #NOWRITE A1 at w → T2 #⇛ #NOWRITE B1 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a₁ b₁)
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta₁ w' e')) w' a b
                            → NOWRITEeq (eqInType u w' (eqta w' e')) w' a b)
        aw w1 e1 p
          = NOWRITEeq-ext-eq {eqInType u w1 (eqta₁ w1 e1)} {eqInType u w1 (eqta w1 e1)} aw0 p
          where
            aw0 : (a₂ b₂ : CTerm) → eqInType u w1 (eqta₁ w1 e1) a₂ b₂ → eqInType u w1 (eqta w1 e1) a₂ b₂
            aw0 a₂ b₂ a∈ rewrite #NOWRITEinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                                | #NOWRITEinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) = snd (inda w1 e1 (eqta₁ w1 e1) a₂ b₂) a∈
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta inda c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → NOWRITEeq (eqInType u w'' (eqta w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta a b w1 e1)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (c₁ : A #⇛ #NOWRITE A1 at w) (c₂ : B #⇛ #NOWRITE B1 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (c₁ : T1 #⇛ #NOWRITE A1 at w) (c₂ : T2 #⇛ #NOWRITE B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt



eqInType-⇛-NOWRITE2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                       (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                       → A #⇛ #NOWRITE A1 at w
                       → B #⇛ #NOWRITE B1 at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                       → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b)
eqInType-⇛-NOWRITE2 u w A B A1 B1 a b eqta exta c₁ c₂ eqt ei ext = concl eqta exta c₁ c₂ a b ei ext
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 B1))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → T1' #⇛ #NOWRITE A1 at w' → T2' #⇛ #NOWRITE B1 at w'
              → (a₁ b₁ : CTerm) → ≡∈Type u' w' eqt' a₁ b₁
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → NOWRITEeq (≡∈Type u' w'' (eqta₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → T1 #⇛ #NOWRITE A1 at w → T2 #⇛ #NOWRITE B1 at w
          → (a₁ b₁ : CTerm) → ≡∈Type u w eqt a₁ b₁
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a₁ b₁)
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext
      = Mod.∀𝕎-□Func M aw ei
      where
        awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
        awexta₁ w1 e1 rewrite #NOWRITEinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                            | #NOWRITEinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeNOWRITE₂ u w T1 T2 A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (≡∈Type u w' (eqta₁ w' e')) w' a b
                            → NOWRITEeq (≡∈Type u w' (eqta w' e')) w' a b)
        aw w1 e1 p rewrite #NOWRITEinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                         | #NOWRITEinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          NOWRITEeq-ext-eq (λ a1 a2 ea → fst (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
-- ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta c₁ c₂ a b ei ext =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) →
            ≡∈Type u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → NOWRITEeq (≡∈Type u w'' (eqta w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-tconst (u ·ᵤ) w A1 B1 eqta exta a b w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
              (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
              a b ez (≤Type-trans-bar₂ e1 x z at ext))

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (c₁ : A #⇛ #NOWRITE A1 at w) (c₂ : B #⇛ #NOWRITE B1 at w) (a b : CTerm) → ≡∈Type u w eqt a b
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b)
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (c₁ : T1 #⇛ #NOWRITE A1 at w) (c₂ : T2 #⇛ #NOWRITE B1 at w) (a b : CTerm) → ≡∈Type u w eqt a b
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b))
        ind
        eqt


eqInType-⇛-NOWRITE-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A #⇛ #NOWRITE A1 at w
                          → B #⇛ #NOWRITE B1 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
                          → eqInType u w eqt a b
eqInType-⇛-NOWRITE-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ eqt ei = concl eqta exta inda c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (inda :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → T1' #⇛ #NOWRITE A1 at w' → T2' #⇛ #NOWRITE B1 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → NOWRITEeq (eqInType u' w'' (eqta₁ w'' e)) w'' a₁ b₁)
              → eqInType u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → T1 #⇛ #NOWRITE A1 at w → T2 #⇛ #NOWRITE B1 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a₁ b₁)
          → eqInType u w eqt a₁ b₁
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' e')) w' a b
                            → NOWRITEeq (eqInType u w' (eqta₁ w' e')) w' a b)
        aw w1 e1 p rewrite #NOWRITEinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                         | #NOWRITEinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          NOWRITEeq-ext-eq (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta inda c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (c₁ : A #⇛ #NOWRITE A1 at w) (c₂ : B #⇛ #NOWRITE B1 at w) (a b : CTerm)
            → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (c₁ : T1 #⇛ #NOWRITE A1 at w) (c₂ : T2 #⇛ #NOWRITE B1 at w) (a b : CTerm)
          → □· w (λ w' e → NOWRITEeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b)
        ind
        eqt


eqInType-⇛-NOWRITE-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                           (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                           → A #⇛ #NOWRITE A1 at w
                           → B #⇛ #NOWRITE B1 at w
                           → (eqt : ≡Types u w A B)
                           → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                           → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b)
                           → ≡∈Type u w eqt a b
eqInType-⇛-NOWRITE-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ eqt ext ei = concl eqta exta c₁ c₂ a b ext ei
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 B1))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → T1' #⇛ #NOWRITE A1 at w' → T2' #⇛ #NOWRITE B1 at w'
              → (a₁ b₁ : CTerm)
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → NOWRITEeq (≡∈Type u' w'' (eqta₁ w'' e)) w'' a₁ b₁)
              → ≡∈Type u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → T1 #⇛ #NOWRITE A1 at w → T2 #⇛ #NOWRITE B1 at w
          → (a₁ b₁ : CTerm)
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a₁ b₁)
          → ≡∈Type u w eqt a₁ b₁
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq (≡∈Type u w' (eqta w' e')) w' a b
                            → NOWRITEeq (≡∈Type u w' (eqta₁ w' e')) w' a b)
        aw w1 e1 p rewrite #NOWRITEinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                         | #NOWRITEinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          NOWRITEeq-ext-eq {≡∈Type u w1 (eqta w1 e1)} {≡∈Type u w1 (eqta₁ w1 e1)} aw2 p
          where
            aw2 : (a₂ b₂ : CTerm) → ≡∈Type u w1 (eqta w1 e1) a₂ b₂ → ≡∈Type u w1 (eqta₁ w1 e1) a₂ b₂
            aw2 a₂ b₂ a∈ = snd (ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeNOWRITE₂ u w T1 T2 A3 A4 x x₁ eqta₁ exta₁ w1 e1))) (eqta w1 e1) a₂ b₂) a∈
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta c₁ c₂ a b ext ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
            a b (≤Type-trans-bar₂ e1 x z at ext) (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (c₁ : A #⇛ #NOWRITE A1 at w) (c₂ : B #⇛ #NOWRITE B1 at w) (a b : CTerm)
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b)
            → ≡∈Type u w eqt a b
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (c₁ : T1 #⇛ #NOWRITE A1 at w) (c₂ : T2 #⇛ #NOWRITE B1 at w) (a b : CTerm)
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → NOWRITEeq (≡∈Type u w' (eqta w' e)) w' a b)
          → ≡∈Type u w eqt a b)
        ind
        eqt


typeSysConds-NOWRITE-local : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE-local u w A B A1 B1 x x₁ eqta exta inda a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → NOWRITEeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → NOWRITEeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-NOWRITE u w1 A B A1 B1 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → NOWRITEeq (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' p x₂ = NOWRITEeq-ext-eq (λ a1 a2 ea → snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) x₂ = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) eqa--}



typeSysConds-NOWRITE : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                       (x : A #⇛ #NOWRITE A1 at w) (x₁ : B #⇛ #NOWRITE B1 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTNOWRITE A1 B1 x x₁ eqta exta)
typeSysConds-NOWRITE u w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-NOWRITE-tsym u w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NOWRITE-ttrans u w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    isym = typeSysConds-NOWRITE-isym u w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-NOWRITE-itrans u w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-NOWRITE-extl1 u w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-NOWRITE-extl2 u w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-NOWRITE-extr1 u w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-NOWRITE-extr2 u w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-NOWRITE-extrevl1 u w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-NOWRITE-extrevl2 u w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-NOWRITE-extrevr1 u w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOWRITE A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-NOWRITE-extrevr2 u w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTNOWRITE A1 B1 x x₁ eqta exta)
    local = typeSysConds-NOWRITE-local u w A B A1 B1 x x₁ eqta exta (∀𝕎-tsp→ext inda)

\end{code}
