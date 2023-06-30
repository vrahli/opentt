\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


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


module type_sys_props_isect {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; <TypeISECTl to <TypeISECTl₂ ; <TypeISECTr to <TypeISECTr₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

--open import theory (bar)
--open import props0 (bar)
--open import ind2 (bar)
--open import terms (bar)
\end{code}



\begin{code}[hide]
ISECTneqNAT : {a b : Term} → ¬ (ISECT a b) ≡ NAT
ISECTneqNAT {a} {b} ()

ISECTneqQNAT : {a b : Term} → ¬ (ISECT a b) ≡ QNAT
ISECTneqQNAT {a} {b} ()

ISECTneqTNAT : {a b : Term} → ¬ (ISECT a b) ≡ TNAT
ISECTneqTNAT {a} {b} ()

ISECTneqLT : {a b : Term} {c d : Term} → ¬ (ISECT a b) ≡ LT c d
ISECTneqLT {a} {b} {c} {d} ()

ISECTneqQLT : {a b : Term} {c d : Term} → ¬ (ISECT a b) ≡ QLT c d
ISECTneqQLT {a} {b} {c} {d} ()

ISECTneqFREE : {a b : Term} → ¬ (ISECT a b) ≡ FREE
ISECTneqFREE {a} {b} ()

ISECTneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (ISECT a b) ≡ EQ c d e
ISECTneqEQ {a} {b} {c} {d} {e} ()

ISECTneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ PI c d
ISECTneqPI {a} {b} {c} {d} ()

ISECTneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ SET c d
ISECTneqSET {a} {b} {c} {d} ()

ISECTneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ UNION c d
ISECTneqUNION {a} {b} {c} {d} ()

ISECTneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ TUNION c d
ISECTneqTUNION {a} {b} {c} {d} ()

--ISECTneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ QTUNION c d
--ISECTneqQTUNION {a} {b} {c} {d} ()

ISECTneqW : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ WT c d
ISECTneqW {a} {b} {c} {d} ()

ISECTneqM : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ MT c d
ISECTneqM {a} {b} {c} {d} ()

ISECTneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ SUM c d
ISECTneqSUM {a} {b} {c} {d} ()

ISECTneqTSQUASH : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ TSQUASH c
ISECTneqTSQUASH {a} {b} {c} ()

--ISECTneqTTRUNC : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ TTRUNC c
--ISECTneqTTRUNC {a} {b} {c} ()

ISECTneqNOWRITE : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ NOWRITE c
ISECTneqNOWRITE {a} {b} {c} ()

ISECTneqSUBSING : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ SUBSING c
ISECTneqSUBSING {a} {b} {c} ()

ISECTneqPURE : {a b : Term} → ¬ (ISECT a b) ≡ PURE
ISECTneqPURE {a} {b} ()

ISECTneqNOSEQ : {a b : Term} → ¬ (ISECT a b) ≡ NOSEQ
ISECTneqNOSEQ {a} {b} ()

ISECTneqTERM : {a b c : Term} → ¬ (ISECT a b) ≡ TERM c
ISECTneqTERM {a} {b} {c} ()

ISECTneqLIFT : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ LIFT c
ISECTneqLIFT {a} {b} {c} ()

ISECTneqDUM : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ DUM c
ISECTneqDUM {a} {b} {c} ()

ISECTneqFFDEFS : {a b : Term} {c d : Term} → ¬ (ISECT a b) ≡ FFDEFS c d
ISECTneqFFDEFS {a} {b} {c} {d} ()

ISECTneqLOWER : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ LOWER c
ISECTneqLOWER {a} {b} {c} ()

ISECTneqSHRINK : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ SHRINK c
ISECTneqSHRINK {a} {b} {c} ()

ISECTneqUNIV : {a b : Term} {n : ℕ} → ¬ (ISECT a b) ≡ UNIV n
ISECTneqUNIV {a} {b} {n} ()



typeSysConds-ISECT-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqTypes u w B A
typeSysConds-ISECT-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTISECT A2 B2 A1 B1 x₁ x syma symb exta' extb'
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


typeSysConds-ISECT-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                            (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                            (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                            → eqTypesTrans u w A B
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt =
  concl x x₁ eqta eqtb exta extb inda indb
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #ISECT A1 B1 at w' → T1' #⇛ #ISECT A2 B2 at w'
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqta₂ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (exta₂ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₂ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (inda₂ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₂ w1 e1)))
              → eqTypes u' w' A T2')
          → A #⇛ #ISECT A1 B1 at w → T1 #⇛ #ISECT A2 B2 at w
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb
      = EQTISECT A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
      where
        eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
        eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (→≡eqTypes (#ISECTinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqta0 w1 e1))

        eqb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 D2)
        eqb w1 e1 = TSP.ttrans (indb w1 e1) D2 (→≡eqTypes (#ISECTinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqtb0 w1 e1)) --

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
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ eqta eqtb exta extb inda indb =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁)
            (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredExtIrr-eqInType-mon eqtb extb w' e')
            (∀𝕎-mon e' inda) (∀𝕎-mon e' indb)

    concl : (c₁ : A #⇛ #ISECT A1 B1 at w) (c₁ : B #⇛ #ISECT A2 B2 at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #ISECT A1 B1 at w) (c₂ : T1 #⇛ #ISECT A2 B2 at w)
           → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
           → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
           → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
           → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
           → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
           → eqTypes u w A T2)
        ind
        eqt


typeSysConds-ISECT-isym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqInTypeSym u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                  → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) g f)
    h w1 e1 (eqa , eqb) = TSP.isym (inda w1 e1) f g eqa , TSP.isym (indb w1 e1) f g eqb



typeSysConds-ISECT-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                         (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f g
                → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) g h
                → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f h)
    aw w1 e1 (ea₁ , ea₂) (eb₁ , eb₂)
      = TSP.itrans (inda w1 e1) f g h ea₁ eb₁ , TSP.itrans (indb w1 e1) f g h ea₂ eb₂


typeSysConds-ISECT-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #ISECT A1 B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #ISECT A1 B1 at w → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta eqtb exta extb inda indb x f g eqi = {!!}
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                            → ISECTeq (eqInType u w' (eqta0 w' e')) (eqInType u w' (eqtb0 w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#ISECTinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x)) =
          ISECTeq-ext-eq {eqInType u w1 (eqta w1 e1)}
            {eqInType u w1 (eqta0 w1 e1)} {eqInType u w1 (eqtb w1 e1)}
            {eqInType u w1 (eqtb0 w1 e1)} {f} {g}
            (TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1)) (TSP.extl1 (indb w1 e1) B4 (eqtb0 w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #ISECT A1 B1 at w) (a b : CTerm)
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #ISECT A1 B1 at w) (a b : CTerm)
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-ISECT-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #ISECT A1 B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #ISECT A1 B1 at w
          → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                            → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#ISECTinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
            ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #ISECT A1 B1 at w)
            (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #ISECT A1 B1 at w)
          → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-ISECT-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #ISECT A2 B2 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #ISECT A2 B2 at w
          → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                            → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#ISECTinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extr1 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #ISECT A2 B2 at w)
            (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #ISECT A2 B2 at w)
          → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-ISECT-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #ISECT A2 B2 at w'
              → (a b : CTerm) → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #ISECT A2 B2 at w
          → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                            → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#ISECTinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1)) (TSP.extr2 (indb w1 e1) B4 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda)(∀𝕎-mon e1 indb)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #ISECT A2 B2 at w)
            (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #ISECT A2 B2 at w)
          → (a b : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-ISECT-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #ISECT A1 B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #ISECT A1 B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                            → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#ISECTinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
          = ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1)) (TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #ISECT A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #ISECT A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b))
        ind
        eqt'



typeSysConds-ISECT-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #ISECT A1 B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #ISECT A1 B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                            → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#ISECTinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
          = ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extrevl2 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #ISECT A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #ISECT A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b))
        ind
        eqt'



typeSysConds-ISECT-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #ISECT A2 B2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #ISECT A2 B2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                            → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#ISECTinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extrevr1 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #ISECT A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #ISECT A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b))
        ind
        eqt'



typeSysConds-ISECT-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #ISECT A2 B2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #ISECT A2 B2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                            → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#ISECTinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1)) (TSP.extrevr2 (indb w1 e1) B4 (eqtb₁ w1 e1)) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #ISECT A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #ISECT A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b))
        ind
        eqt'



eqInType-⇛-ISECT : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                    (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                    (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                    (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                    → A #⇛ #ISECT A1 B1 at w
                    → B #⇛ #ISECT A2 B2 at w
                    → (eqt : eqTypes u w A B)
                    → eqInType u w eqt a b
                    → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ eqt eqi =
  concl eqta eqtb exta extb inda indb c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → (inda₁ :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb₁ :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1)))
              → T1' #⇛ #ISECT A1 B1 at w' → T2' #⇛ #ISECT A2 B2 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → T1 #⇛ #ISECT A1 B1 at w → T2 #⇛ #ISECT A2 B2 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a₁ b₁)
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) a b
                            → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) a b)
        aw w1 e1 p
          = ISECTeq-ext-eq {eqInType u w1 (eqta₁ w1 e1)} {eqInType u w1 (eqta w1 e1)} {eqInType u w1 (eqtb₁ w1 e1)} {eqInType u w1 (eqtb w1 e1)} {a} {b} aw1 aw2 p
          where
            aw1 : (a₂ b₂ : CTerm) → eqInType u w1 (eqta₁ w1 e1) a₂ b₂ → eqInType u w1 (eqta w1 e1) a₂ b₂
            aw1 a₂ b₂ a∈
              rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                    | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
              = snd (inda w1 e1 (eqta₁ w1 e1) a₂ b₂) a∈

            aw2 : (a₂ b₂ : CTerm) → eqInType u w1 (eqtb₁ w1 e1) a₂ b₂ → eqInType u w1 (eqtb w1 e1) a₂ b₂
            aw2 a₂ b₂ a∈
              rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                    | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
              = snd (indb w1 e1 (eqtb₁ w1 e1) a₂ b₂) a∈
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
            (c₁ : A #⇛ #ISECT A1 B1 at w) (c₂ : B #⇛ #ISECT A2 B2 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → (c₁ : T1 #⇛ #ISECT A1 B1 at w) (c₂ : T2 #⇛ #ISECT A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b))
        ind
        eqt




eqInType-⇛-ISECT2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                     → A #⇛ #ISECT A1 B1 at w
                     → B #⇛ #ISECT A2 B2 at w
                     → (eqt : ≡Types u w A B)
                     → (eqi : ≡∈Type u w eqt a b)
                     → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                     → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ eqt ei ext =
  concl eqta eqtb exta extb c₁ c₂ a b ei ext
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' B1 B2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → T1' #⇛ #ISECT A1 B1 at w' → T2' #⇛ #ISECT A2 B2 at w'
              → (a₁ b₁ : CTerm) → ≡∈Type u' w' eqt' a₁ b₁
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → ISECTeq (≡∈Type u' w'' (eqta₁ w'' e)) (≡∈Type u' w'' (eqtb₁ w'' e)) a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqtb w₂ e) a₁ b₁))
          → T1 #⇛ #ISECT A1 B1 at w → T2 #⇛ #ISECT A2 B2 at w
          → (a₁ b₁ : CTerm) → ≡∈Type u w eqt a₁ b₁
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a₁ b₁)
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) a b
                            → ISECTeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) a b)
        aw w1 e1 p
          rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = ISECTeq-ext-eq {_} {_} {_} {_} {a} {b} (λ a1 a2 ea → fst (awexta₁ (eqta w1 e1) a1 a2) ea) (λ a1 a2 ea → fst (awextb₁ (eqtb w1 e1) a1 a2) ea) p
            where
              awexta₁ : eqInTypeExt (eqta₁ w1 e1)
              awexta₁ = ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeISECTl₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

              awextb₁ : eqInTypeExt (eqtb₁ w1 e1)
              awextb₁ = ext (eqtb₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeISECTr₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt c₁ x))
-- ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqta₁ exta₁ eqx) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb c₁ c₂ a b ei ext =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) →
            ≡∈Type u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → ISECTeq (≡∈Type u w'' (eqta w'' x)) (≡∈Type u w'' (eqtb w'' x)) a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-isect (u ·ᵤ) w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
              (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
              (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
              (⇛-mon e1 c₁) (⇛-mon e1 c₂)
              a b ez (≤Type-trans-bar₂ e1 x z at ext))

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
            (c₁ : A #⇛ #ISECT A1 B1 at w) (c₂ : B #⇛ #ISECT A2 B2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
          → (c₁ : T1 #⇛ #ISECT A1 B1 at w) (c₂ : T2 #⇛ #ISECT A2 B2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b))
        ind
        eqt




eqInType-⇛-ISECT-rev : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                        → A #⇛ #ISECT A1 B1 at w
                        → B #⇛ #ISECT A2 B2 at w
                        → (eqt : eqTypes u w A B)
                        → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
                        → eqInType u w eqt a b
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ eqt ei =
  concl eqta eqtb exta extb inda indb c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → (inda :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1)))
              → T1' #⇛ #ISECT A1 B1 at w' → T2' #⇛ #ISECT A2 B2 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → ISECTeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) a₁ b₁)
              → eqInType u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → T1 #⇛ #ISECT A1 B1 at w → T2 #⇛ #ISECT A2 B2 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a₁ b₁)
          → eqInType u w eqt a₁ b₁
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) a b
                            → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) a b)
        aw w1 e1 p
          rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = ISECTeq-ext-eq {_} {_} {_} {_} {a} {b} (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) (λ a1 a2 ea → fst (indb w1 e1 (eqtb₁ w1 e1) a1 a2) ea) p
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
            (c₁ : A #⇛ #ISECT A1 B1 at w) (c₂ : B #⇛ #ISECT A2 B2 at w) (a b : CTerm)
            → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → (c₁ : T1 #⇛ #ISECT A1 B1 at w) (c₂ : T2 #⇛ #ISECT A2 B2 at w) (a b : CTerm)
          → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
          → eqInType u w eqt a b)
        ind
        eqt




eqInType-⇛-ISECT-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                         (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                         → A #⇛ #ISECT A1 B1 at w
                         → B #⇛ #ISECT A2 B2 at w
                         → (eqt : ≡Types u w A B)
                         → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                         → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
                         → ≡∈Type u w eqt a b
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ eqt ext ei =
  concl eqta eqtb exta extb c₁ c₂ a b ext ei
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' B1 B2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → T1' #⇛ #ISECT A1 B1 at w' → T2' #⇛ #ISECT A2 B2 at w'
              → (a₁ b₁ : CTerm)
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → ISECTeq (≡∈Type u' w'' (eqta₁ w'' e)) (≡∈Type u' w'' (eqtb₁ w'' e)) a₁ b₁)
              → ≡∈Type u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqtb w₂ e) a₁ b₁))
          → T1 #⇛ #ISECT A1 B1 at w → T2 #⇛ #ISECT A2 B2 at w
          → (a₁ b₁ : CTerm)
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a₁ b₁)
          → ≡∈Type u w eqt a₁ b₁
    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) a b
                            → ISECTeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) a b)
        aw w1 e1 p
          rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = ISECTeq-ext-eq {≡∈Type u w1 (eqta w1 e1)} {≡∈Type u w1 (eqta₁ w1 e1)} {≡∈Type u w1 (eqtb w1 e1)} {≡∈Type u w1 (eqtb₁ w1 e1)} {a} {b} aw1 aw2 p
          where
            aw1 : (a₂ b₂ : CTerm) → ≡∈Type u w1 (eqta w1 e1) a₂ b₂ → ≡∈Type u w1 (eqta₁ w1 e1) a₂ b₂
            aw1 a₂ b₂ a∈ = snd (ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeISECTl₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1))) (eqta w1 e1) a₂ b₂) a∈

            aw2 : (a₂ b₂ : CTerm) → ≡∈Type u w1 (eqtb w1 e1) a₂ b₂ → ≡∈Type u w1 (eqtb₁ w1 e1) a₂ b₂
            aw2 a₂ b₂ a∈ = snd (ext (eqtb₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeISECTr₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1))) (eqtb w1 e1) a₂ b₂) a∈
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqNOWRITE (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb c₁ c₂ a b ext ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂)
            a b (≤Type-trans-bar₂ e1 x z at ext) (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
            (c₁ : A #⇛ #ISECT A1 B1 at w) (c₂ : B #⇛ #ISECT A2 B2 at w) (a b : CTerm)
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
            → ≡∈Type u w eqt a b
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
          → (c₁ : T1 #⇛ #ISECT A1 B1 at w) (c₂ : T2 #⇛ #ISECT A2 B2 at w) (a b : CTerm)
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
          → ≡∈Type u w eqt a b)
        ind
        eqt




typeSysConds-ISECT-local : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                           → eqInTypeLocal (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → ISECTeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (eqInType u w'' (eqtb w'' (⊑-trans· e1 e))) a b)
        aw' = eqInType-⇛-ISECT u w1 A B A1 A2 B1 B2 a b
                               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
                               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
                               (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
                               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → ISECTeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) a b
                                → (x₂ : w ⊑· w') → ISECTeq (eqInType u w' (eqta w' x₂)) (eqInType u w' (eqtb w' x₂)) a b)
        aw'' w' e' (eqa , eqb) x₂ = eqa' , eqb'
          where
            eqa' : eqInType u w' (eqta w' x₂) a b
            eqa' = exta a b w' (⊑-trans· e1 e') x₂ eqa

            eqb' : eqInType u w' (eqtb w' x₂) a b
            eqb' = extb a b w' (⊑-trans· e1 e') x₂ eqb



typeSysConds-ISECT : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                     (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                     → TSP {u} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-ISECT-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-ISECT-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-ISECT-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-ISECT-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-tsp→ext indb)
\end{code}
