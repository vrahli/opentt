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


module type_sys_props_ttrunc {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; <TypeTTRUNC to <TypeTTRUNC₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
TTRUNCneqNAT : {a : Term} → ¬ (TTRUNC a) ≡ NAT
TTRUNCneqNAT {a} ()

TTRUNCneqQNAT : {a : Term} → ¬ (TTRUNC a) ≡ QNAT
TTRUNCneqQNAT {a} ()

TTRUNCneqTNAT : {a : Term} → ¬ (TTRUNC a) ≡ TNAT
TTRUNCneqTNAT {a} ()

TTRUNCneqLT : {a : Term} {c d : Term} → ¬ (TTRUNC a) ≡ LT c d
TTRUNCneqLT {a} {c} {d} ()

TTRUNCneqQLT : {a : Term} {c d : Term} → ¬ (TTRUNC a) ≡ QLT c d
TTRUNCneqQLT {a} {c} {d} ()

TTRUNCneqFREE : {a : Term} → ¬ (TTRUNC a) ≡ FREE
TTRUNCneqFREE {a} ()

TTRUNCneqPI : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ PI c d
TTRUNCneqPI {a} {c} {d} ()

TTRUNCneqW : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ WT c d
TTRUNCneqW {a} {c} {d} ()

TTRUNCneqM : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ MT c d
TTRUNCneqM {a} {c} {d} ()

TTRUNCneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ SUM c d
TTRUNCneqSUM {a} {c} {d} ()

TTRUNCneqSET : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ SET c d
TTRUNCneqSET {a} {c} {d} ()

TTRUNCneqISECT : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ ISECT c d
TTRUNCneqISECT {a} {c} {d} ()

TTRUNCneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ TUNION c d
TTRUNCneqTUNION {a} {c} {d} ()

TTRUNCneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ UNION c d
TTRUNCneqUNION {a} {c} {d} ()

TTRUNCneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ QTUNION c d
TTRUNCneqQTUNION {a} {c} {d} ()

TTRUNCneqEQ : {a : Term} {c d e : Term} → ¬ (TTRUNC a) ≡ EQ c d e
TTRUNCneqEQ {a} {c} {d} {e} ()

TTRUNCneqDUM : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ DUM c
TTRUNCneqDUM {a} {c} ()

TTRUNCneqFFDEFS : {a : Term} {c d : Term} → ¬ (TTRUNC a) ≡ FFDEFS c d
TTRUNCneqFFDEFS {a} {c} {d} ()

TTRUNCneqLIFT : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ LIFT c
TTRUNCneqLIFT {a} {c} ()

TTRUNCneqTCONST : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ TCONST c
TTRUNCneqTCONST {a} {c} ()

TTRUNCneqSUBSING : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ SUBSING c
TTRUNCneqSUBSING {a} {c} ()

TTRUNCneqPURE : {a : Term} → ¬ (TTRUNC a) ≡ PURE
TTRUNCneqPURE {a} ()

TTRUNCneqNOSEQ : {a : Term} → ¬ (TTRUNC a) ≡ NOSEQ
TTRUNCneqNOSEQ {a} ()

TTRUNCneqTERM : {a c : Term} → ¬ (TTRUNC a) ≡ TERM c
TTRUNCneqTERM {a} {c} ()

TTRUNCneqTSQUASH : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ TSQUASH c
TTRUNCneqTSQUASH {a} {c} ()

TTRUNCneqLOWER : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ LOWER c
TTRUNCneqLOWER {a} {c} ()

TTRUNCneqSHRINK : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ SHRINK c
TTRUNCneqSHRINK {a} {c} ()

TTRUNCneqUNIV : {a : Term} {n : ℕ} → ¬ (TTRUNC a) ≡ UNIV n
TTRUNCneqUNIV {a} {n} ()


typeSysConds-TTRUNC-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-TTRUNC-tsym u w A B A1 B1 x x₁ eqta exta inda =
  EQTTRUNC B1 A1 x₁ x syma exta'
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


typeSysConds-TTRUNC-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C eqt = concl x x₁ eqta exta inda
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #TTRUNC A1 at w' → T1' #⇛ #TTRUNC B1 at w'
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → eqTypes u' w' A T2')
          → A #⇛ #TTRUNC A1 at w → T1 #⇛ #TTRUNC B1 at w
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda
      = EQTTRUNC A1 A4 x y₁ eqa exta'
      where
        eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A4)
        eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (→≡eqTypes (#TTRUNCinj {A3} {B1} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqtA w1 e1))

        exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
        exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) A4 (eqa w' e2) a b ei2
          where
            ei1 : eqInType u w' (eqta w' e1) a b
            ei1 = TSP.extrevl1 (inda w' e1) A4 (eqa w' e1) a b ei

            ei2 : eqInType u w' (eqta w' e2) a b
            ei2 = exta a b w' e1 e2 ei1
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ eqta exta inda = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ eqta exta inda =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' inda)

    concl : (c₁ : A #⇛ #TTRUNC A1 at w) (c₁ : B #⇛ #TTRUNC B1 at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #TTRUNC A1 at w) (c₂ : T1 #⇛ #TTRUNC B1 at w)
           → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
           → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
           → eqTypes u w A T2)
        ind
        eqt



typeSysConds-TTRUNC-isym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-isym u w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                  → TTRUNCeq (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 p = TTRUNCeq-sym (TSP.isym (inda w1 e1)) p
{--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , z) =
      {--≈C-sym {w1} {f} {g}--} c₃ , b , a , isv₂ , isv₁ , c₂ , c₁ , TSP.isym (inda w1 e1) a b z
--}



typeSysConds-TTRUNC-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-itrans u w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                TTRUNCeq (eqInType u w' (eqta w' e)) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e)) w' g h
                → TTRUNCeq (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 p₁ p₂ = TTRUNCeq-trans p₁ p₂
{--(c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) (d₃ , b₁ , b₂ , isx₁ , isx₂ , d₁ , d₂ , eb) =
      {--≈C-trans {w1} {f} {g} {h} c₃--} d₃ ,
      a₁ , a₂ , isv₁ , isv₂ ,
      c₁ ,
      {!!} , --∼C-trans {w1} {h} {g} {a₂} (∼C-sym {w1} {g} {h} (≈C-∼C {w1} {g} {h} d₃)) c₂ ,
      ea
--}



typeSysConds-TTRUNC-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #TTRUNC A1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #TTRUNC A1 at w → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta exta inda x f g eqi = {!!}
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A3} {A1} (#⇛-val-det {_} {T1} tt tt y x)) =
          TTRUNCeq-ext-eq {eqInType u w1 (eqta w1 e1)} {eqInType u w1 (eqtA w1 e1)} {w1} {f} {g}
            (TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y))
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
            (comp : A #⇛ #TTRUNC A1 at w) (a b : CTerm)
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #TTRUNC A1 at w) (a b : CTerm)
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TTRUNC-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #TTRUNC A1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #TTRUNC A1 at w
          → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A4} {A1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
          TTRUNCeq-ext-eq (TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y₁))
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
            (comp : A #⇛ #TTRUNC A1 at w)
            (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          →  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #TTRUNC A1 at w)
          → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TTRUNC-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #TTRUNC B1 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #TTRUNC B1 at w
          → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A4} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x₁)) =
          TTRUNCeq-ext-eq (TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y₁))
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
            (comp : B #⇛ #TTRUNC B1 at w)
            (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #TTRUNC B1 at w)
          → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TTRUNC-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #TTRUNC B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #TTRUNC B1 at w
          → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A3} {B1} (#⇛-val-det {_} {T1} tt tt y x₁)) =
          TTRUNCeq-ext-eq (TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y))
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
            (comp : B #⇛ #TTRUNC B1 at w)
            (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #TTRUNC B1 at w)
          → (a b : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TTRUNC-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #TTRUNC A1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #TTRUNC A1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A3} {A1} (#⇛-val-det {_} {T1} tt tt y x)) =
          TTRUNCeq-ext-eq (TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : A #⇛ #TTRUNC A1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #TTRUNC A1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



typeSysConds-TTRUNC-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #TTRUNC A1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #TTRUNC A1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A4} {A1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
          TTRUNCeq-ext-eq (TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : A #⇛ #TTRUNC A1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #TTRUNC A1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



typeSysConds-TTRUNC-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T2' #⇛ #TTRUNC B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T2 #⇛ #TTRUNC B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A4} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x₁)) =
          TTRUNCeq-ext-eq (TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : B #⇛ #TTRUNC B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T2 #⇛ #TTRUNC B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



typeSysConds-TTRUNC-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C eqt' = concl eqta exta inda x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → T1' #⇛ #TTRUNC B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → T1 #⇛ #TTRUNC B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                            → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
        aw w1 e1 p rewrite sym (#TTRUNCinj {A3} {B1} (#⇛-val-det {_} {T1} tt tt y x₁)) =
          TTRUNCeq-ext-eq (TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta exta inda x₁ f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta exta inda x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (comp : B #⇛ #TTRUNC B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (comp : T1 #⇛ #TTRUNC B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt'



eqInType-⇛-TTRUNC : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A #⇛ #TTRUNC A1 at w
                      → B #⇛ #TTRUNC B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ eqt eqi = concl eqta exta inda c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (inda₁ :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → T1' #⇛ #TTRUNC A1 at w' → T2' #⇛ #TTRUNC B1 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → T1 #⇛ #TTRUNC A1 at w → T2 #⇛ #TTRUNC B1 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a₁ b₁)
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta₁ w' e')) w' a b
                            → TTRUNCeq (eqInType u w' (eqta w' e')) w' a b)
        aw w1 e1 p
          = TTRUNCeq-ext-eq {eqInType u w1 (eqta₁ w1 e1)} {eqInType u w1 (eqta w1 e1)} aw0 p
          where
            aw0 : (a₂ b₂ : CTerm) → eqInType u w1 (eqta₁ w1 e1) a₂ b₂ → eqInType u w1 (eqta w1 e1) a₂ b₂
            aw0 a₂ b₂ a∈ rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                                | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) = snd (inda w1 e1 (eqta₁ w1 e1) a₂ b₂) a∈
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta inda c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta a b w1 e1)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (c₁ : A #⇛ #TTRUNC A1 at w) (c₂ : B #⇛ #TTRUNC B1 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (c₁ : T1 #⇛ #TTRUNC A1 at w) (c₂ : T2 #⇛ #TTRUNC B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b))
        ind
        eqt



eqInType-⇛-TTRUNC2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                       (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                       → A #⇛ #TTRUNC A1 at w
                       → B #⇛ #TTRUNC B1 at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                       → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ eqt ei ext = concl eqta exta c₁ c₂ a b ei ext
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 B1))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → T1' #⇛ #TTRUNC A1 at w' → T2' #⇛ #TTRUNC B1 at w'
              → (a₁ b₁ : CTerm) → ≡∈Type u' w' eqt' a₁ b₁
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → TTRUNCeq (≡∈Type u' w'' (eqta₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → T1 #⇛ #TTRUNC A1 at w → T2 #⇛ #TTRUNC B1 at w
          → (a₁ b₁ : CTerm) → ≡∈Type u w eqt a₁ b₁
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a₁ b₁)
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext
      = Mod.∀𝕎-□Func M aw ei
      where
        awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
        awexta₁ w1 e1 rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                            | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeTTRUNC₂ u w T1 T2 A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (≡∈Type u w' (eqta₁ w' e')) w' a b
                            → TTRUNCeq (≡∈Type u w' (eqta w' e')) w' a b)
        aw w1 e1 p rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                         | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          TTRUNCeq-ext-eq (λ a1 a2 ea → fst (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
-- ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta c₁ c₂ a b ei ext = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta c₁ c₂ a b ei ext =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) →
            ≡∈Type u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → TTRUNCeq (≡∈Type u w'' (eqta w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-ttrunc (u ·ᵤ) w A1 B1 eqta exta a b w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
              (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
              a b ez (≤Type-trans-bar₂ e1 x z at ext))

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (c₁ : A #⇛ #TTRUNC A1 at w) (c₂ : B #⇛ #TTRUNC B1 at w) (a b : CTerm) → ≡∈Type u w eqt a b
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (c₁ : T1 #⇛ #TTRUNC A1 at w) (c₂ : T2 #⇛ #TTRUNC B1 at w) (a b : CTerm) → ≡∈Type u w eqt a b
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b))
        ind
        eqt




eqInType-⇛-TTRUNC-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A #⇛ #TTRUNC A1 at w
                          → B #⇛ #TTRUNC B1 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
                          → eqInType u w eqt a b
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ eqt ei = concl eqta exta inda c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 B1))
              → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (inda :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → T1' #⇛ #TTRUNC A1 at w' → T2' #⇛ #TTRUNC B1 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → TTRUNCeq (eqInType u' w'' (eqta₁ w'' e)) w'' a₁ b₁)
              → eqInType u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → T1 #⇛ #TTRUNC A1 at w → T2 #⇛ #TTRUNC B1 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a₁ b₁)
          → eqInType u w eqt a₁ b₁
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' a b
                            → TTRUNCeq (eqInType u w' (eqta₁ w' e')) w' a b)
        aw w1 e1 p rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                         | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          TTRUNCeq-ext-eq (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta inda c₁ c₂ a b ei = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta inda c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (c₁ : A #⇛ #TTRUNC A1 at w) (c₂ : B #⇛ #TTRUNC B1 at w) (a b : CTerm)
            → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (c₁ : T1 #⇛ #TTRUNC A1 at w) (c₂ : T2 #⇛ #TTRUNC B1 at w) (a b : CTerm)
          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
          → eqInType u w eqt a b)
        ind
        eqt



eqInType-⇛-TTRUNC-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                           (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                           → A #⇛ #TTRUNC A1 at w
                           → B #⇛ #TTRUNC B1 at w
                           → (eqt : ≡Types u w A B)
                           → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                           → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
                           → ≡∈Type u w eqt a b
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ eqt ext ei = concl eqta exta c₁ c₂ a b ext ei
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 B1))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → T1' #⇛ #TTRUNC A1 at w' → T2' #⇛ #TTRUNC B1 at w'
              → (a₁ b₁ : CTerm)
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → TTRUNCeq (≡∈Type u' w'' (eqta₁ w'' e)) w'' a₁ b₁)
              → ≡∈Type u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → T1 #⇛ #TTRUNC A1 at w → T2 #⇛ #TTRUNC B1 at w
          → (a₁ b₁ : CTerm)
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a₁ b₁)
          → ≡∈Type u w eqt a₁ b₁
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TTRUNCeq (≡∈Type u w' (eqta w' e')) w' a b
                            → TTRUNCeq (≡∈Type u w' (eqta₁ w' e')) w' a b)
        aw w1 e1 p rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                         | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {T2} tt tt c₂ x₁) =
          TTRUNCeq-ext-eq {≡∈Type u w1 (eqta w1 e1)} {≡∈Type u w1 (eqta₁ w1 e1)} aw2 p
          where
            aw2 : (a₂ b₂ : CTerm) → ≡∈Type u w1 (eqta w1 e1) a₂ b₂ → ≡∈Type u w1 (eqta₁ w1 e1) a₂ b₂
            aw2 a₂ b₂ a∈ = snd (ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeTTRUNC₂ u w T1 T2 A3 A4 x x₁ eqta₁ exta₁ w1 e1))) (eqta w1 e1) a₂ b₂) a∈
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta exta c₁ c₂ a b ext ei = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta exta c₁ c₂ a b ext ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
            a b (≤Type-trans-bar₂ e1 x z at ext) (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (c₁ : A #⇛ #TTRUNC A1 at w) (c₂ : B #⇛ #TTRUNC B1 at w) (a b : CTerm)
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
            → ≡∈Type u w eqt a b
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (c₁ : T1 #⇛ #TTRUNC A1 at w) (c₂ : T2 #⇛ #TTRUNC B1 at w) (a b : CTerm)
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
          → ≡∈Type u w eqt a b)
        ind
        eqt



typeSysConds-TTRUNC-local : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-local u w A B A1 B1 x x₁ eqta exta inda a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → TTRUNCeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-TTRUNC u w1 A B A1 B1 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → TTRUNCeq (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' p x₂ = TTRUNCeq-ext-eq (λ a1 a2 ea → snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) x₂ = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) eqa--}



typeSysConds-TTRUNC : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                       (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC u w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TTRUNC-tsym u w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    isym = typeSysConds-TTRUNC-isym u w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-TTRUNC-itrans u w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTTRUNC A1 B1 x x₁ eqta exta)
    local = typeSysConds-TTRUNC-local u w A B A1 B1 x x₁ eqta exta (∀𝕎-tsp→ext inda)
\end{code}
