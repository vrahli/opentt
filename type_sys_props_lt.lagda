\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


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
open import choiceExt
open import newChoice
open import mod
open import encode


module type_sys_props_lt {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
--LTneqNAT : {u v : Term} → ¬ LT u v ≡ NAT
--LTneqNAT {u} {v} ()

LTneqQNAT : {u v : Term} → ¬ LT u v ≡ QNAT
LTneqQNAT {u} {v} ()

--LTneqTNAT : {u v : Term} → ¬ LT u v ≡ TNAT
--LTneqTNAT {u} {v} ()

LTneqQLT : {u v : Term} {c d : Term} → ¬ LT u v ≡ QLT c d
LTneqQLT {u} {v} {c} {d} ()

LTneqFREE : {u v : Term} → ¬ LT u v ≡ FREE
LTneqFREE {u} {v} ()

LTneqPI : {u v : Term} {c d : Term} → ¬ LT u v ≡ PI c d
LTneqPI {u} {v} {c} {d} ()

LTneqW : {u v : Term} {c d e : Term} → ¬ LT u v ≡ WT c d e
LTneqW {u} {v} {c} {d} {e} ()

LTneqM : {u v : Term} {c d e : Term} → ¬ LT u v ≡ MT c d e
LTneqM {u} {v} {c} {d} {e} ()

LTneqSUM : {u v : Term} {c d : Term} → ¬ LT u v ≡ SUM c d
LTneqSUM {u} {v} {c} {d} ()

LTneqSET : {u v : Term} {c d : Term} → ¬ LT u v ≡ SET c d
LTneqSET {u} {v} {c} {d} ()

LTneqTUNION : {u v : Term} {c d : Term} → ¬ LT u v ≡ TUNION c d
LTneqTUNION {u} {v} {c} {d} ()

LTneqUNION : {u v : Term} {c d : Term} → ¬ LT u v ≡ UNION c d
LTneqUNION {u} {v} {c} {d} ()

LTneqISECT : {u v : Term} {c d : Term} → ¬ LT u v ≡ ISECT c d
LTneqISECT {u} {v} {c} {d} ()

--LTneqQTUNION : {u v : Term} {c d : Term} → ¬ LT u v ≡ QTUNION c d
--LTneqQTUNION {u} {v} {c} {d} ()

LTneqEQ : {u v : Term} {c d e : Term} → ¬ LT u v ≡ EQ c d e
LTneqEQ {u} {v} {c} {d} {e} ()

--LTneqTSQUASH : {u v : Term} {c : Term} → ¬ LT u v ≡ TSQUASH c
--LTneqTSQUASH {u} {v} {c} ()

--LTneqTTRUNC : {u v : Term} {c : Term} → ¬ LT u v ≡ TTRUNC c
--LTneqTTRUNC {u} {v} {c} ()

LTneqNOWRITE : {u v : Term} → ¬ LT u v ≡ NOWRITE
LTneqNOWRITE {u} {v} ()

LTneqNOREAD : {u v : Term} → ¬ LT u v ≡ NOREAD
LTneqNOREAD {u} {v} ()

LTneqSUBSING : {u v : Term} {c : Term} → ¬ LT u v ≡ SUBSING c
LTneqSUBSING {u} {v} {c} ()

LTneqPURE : {u v : Term} → ¬ LT u v ≡ PURE
LTneqPURE {u} {v} ()

LTneqNOSEQ : {u v : Term} → ¬ LT u v ≡ NOSEQ
LTneqNOSEQ {u} {v} ()

LTneqNOENC : {u v : Term} → ¬ LT u v ≡ NOENC
LTneqNOENC {u} {v} ()

LTneqTERM : {u v c : Term} → ¬ LT u v ≡ TERM c
LTneqTERM {u} {v} {c} ()

--LTneqLIFT : {u v : Term} {c : Term} → ¬ LT u v ≡ LIFT c
--LTneqLIFT {u} {v} {c} ()

LTneqPARTIAL : {u v : Term} {c : Term} → ¬ LT u v ≡ PARTIAL c
LTneqPARTIAL {u} {v} {c} ()

LTneqFFDEFS : {u v : Term} {c d : Term} → ¬ LT u v ≡ FFDEFS c d
LTneqFFDEFS {u} {v} {c} {d} ()

LTneqLOWER : {u v : Term} {c : Term} → ¬ LT u v ≡ LOWER c
LTneqLOWER {u} {v} {c} ()

LTneqSHRINK : {u v : Term} {c : Term} → ¬ LT u v ≡ SHRINK c
LTneqSHRINK {u} {v} {c} ()

LTneqUNIV : {u v : Term} {n : ℕ} → ¬ LT u v ≡ UNIV n
LTneqUNIV {u} {v} {n} ()


→#strongMonEq : (w : 𝕎·) (a1 a2 b1 b2 : CTerm)
              → a1 ≡ b1
              → a2 ≡ b2
              → #strongMonEq w a1 a2
              → #strongMonEq w b1 b2
→#strongMonEq w a1 a2 b1 b2 refl refl s = s


→#lift-<NUM-pair : (w : 𝕎·) (a1 a2 b1 b2 : CTerm)
                 → a1 ≡ b1
                 → a2 ≡ b2
                 → #lift-<NUM-pair w a1 a2
                 → #lift-<NUM-pair w b1 b2
→#lift-<NUM-pair w a1 a2 b1 b2 refl refl s = s


typeSysConds-LT-ttrans : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                         (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqTypesTrans u w A B
typeSysConds-LT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt = concl x x₁ s s₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #LT a1 b1 at w' → T1' #⇛ #LT a2 b2 at w'
              → #strongMonEq w' a1 a2
              → #strongMonEq w' b1 b2
              → eqTypes u' w' A T2')
          → A #⇛ #LT a1 b1 at w → T1 #⇛ #LT a2 b2 at w
          → #strongMonEq w a1 a2
          → #strongMonEq w b1 b2
          → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ s s₁ =
      EQTLT a1 c2 b1 d2 x y₁
        (strongMonEq-trans s  (→#strongMonEq w c1 c2 a2 c2 (CTerm≡ (LTinj1 (⇛-val-det tt tt y x₁))) refl x₄))
        (strongMonEq-trans s₁ (→#strongMonEq w d1 d2 b2 d2 (CTerm≡ (LTinj2 (⇛-val-det tt tt y x₁))) refl x₅))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ s s₁ = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ s s₁ = ⊥-elim (LTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ s s₁ = ⊥-elim (LTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ s s₁ = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (LTneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ s s₁ = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ s s₁ = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ s s₁ = ⊥-elim (LTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁ s s₁ = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ s s₁ = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ s s₁ = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ s s₁ =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁) (#strongMonEq-mon {a1} {a2} s w' e') (#strongMonEq-mon {b1} {b2} s₁ w' e')

    concl : (c₁ : A #⇛ #LT a1 b1 at w) (c₁ : B #⇛ #LT a2 b2 at w)
          → #strongMonEq w a1 a2
          → #strongMonEq w b1 b2
          → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #LT a1 b1 at w) (c₂ : T1 #⇛ #LT a2 b2 at w)
           → #strongMonEq w a1 a2
           → #strongMonEq w b1 b2
           → eqTypes u w A T2)
        ind
        eqt



typeSysConds-LT-extl1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                        (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                      → eqInTypeExtL1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl x s s₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → T1' #⇛ #LT a1 b1 at w'
              → #strongMonEq w' a1 a2
              → #strongMonEq w' b1 b2
              → (a b : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → T1 #⇛ #LT a1 b1 at w
          → #strongMonEq w a1 a2
          → #strongMonEq w b1 b2
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x s s₁ f g eqi =
      Mod.∀𝕎-□Func M
        (λ w1 e1 q → →#lift-<NUM-pair w1 a1 b1 c1 d1 (CTerm≡ (LTinj1 (⇛-val-det tt tt x y))) (CTerm≡ (LTinj2 (⇛-val-det tt tt x y))) q)
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x s s₁ f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x s s₁ f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x s s₁ f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x s s₁ f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x s s₁ f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x s s₁ f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x s s₁ f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x s s₁ f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x s s₁ f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x s s₁ f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x s s₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
             (⇛-mon e1 x) (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1) f g
             (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #LT a1 b1 at w)
            (s₁ : #strongMonEq w a1 a2)
            (s₂ : #strongMonEq w b1 b2)
            → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #LT a1 b1 at w)
          → #strongMonEq w a1 a2
          → #strongMonEq w b1 b2
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-LT-extl2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                          (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                          → eqInTypeExtL2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T2' #⇛ #LT a1 b1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T2 #⇛ #LT a1 b1 at w
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi =
      strongMonEq-preserves-□· {_} {a1} {b1} {c1} {d1}
        (→#strongMonEq w c1 c2 c1 a1 refl (CTerm≡ (LTinj1 (⇛-val-det tt tt y₁ x))) x₄)
        (→#strongMonEq w d1 d2 d1 b1 refl (CTerm≡ (LTinj2 (⇛-val-det tt tt y₁ x))) x₅)
        eqi --⊥-elim (LTneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x y₁))
{--      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                            → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#ISECTinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
            ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1)) p--}
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : A #⇛ #LT a1 b1 at w)
            (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T2 #⇛ #LT a1 b1 at w)
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-LT-extr1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                        (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                      → eqInTypeExtR1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T2' #⇛ #LT a2 b2 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T2 #⇛ #LT a2 b2 at w
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      strongMonEq-preserves-□· {_} {a1} {b1} {c1} {d1}
        (strongMonEq-trans x₄ (strongMonEq-sym (→#strongMonEq w a1 a2 a1 c2 refl (CTerm≡ (LTinj1 (⇛-val-det tt tt x₁ y₁))) s)))
        (strongMonEq-trans x₅ (strongMonEq-sym (→#strongMonEq w b1 b2 b1 d2 refl (CTerm≡ (LTinj2 (⇛-val-det tt tt x₁ y₁))) s₁)))
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : B #⇛ #LT a2 b2 at w)
            (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T2 #⇛ #LT a2 b2 at w)
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-LT-extr2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                        (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                      → eqInTypeExtR2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T1' #⇛ #LT a2 b2 at w'
              → (a b : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T1 #⇛ #LT a2 b2 at w
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      strongMonEq-preserves-□· {_} {a1} {b1} {c1} {d1}
        (strongMonEq-sym (→#strongMonEq w a1 a2 a1 c1 refl (CTerm≡ (LTinj1 (⇛-val-det tt tt x₁ y))) s))
        (strongMonEq-sym (→#strongMonEq w b1 b2 b1 d1 refl (CTerm≡ (LTinj2 (⇛-val-det tt tt x₁ y))) s₁))
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : B #⇛ #LT a2 b2 at w)
            (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T1 #⇛ #LT a2 b2 at w)
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-LT-extrevl1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                           → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T1' #⇛ #LT a1 b1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T1 #⇛ #LT a1 b1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi =
      strongMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (→#strongMonEq w c1 c1 a1 c1 (CTerm≡ (LTinj1 (⇛-val-det tt tt y x))) refl (strongMonEq-refl x₄))
        (→#strongMonEq w d1 d1 b1 d1 (CTerm≡ (LTinj2 (⇛-val-det tt tt y x))) refl (strongMonEq-refl x₅))
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → #lift-<NUM-pair w'' a1 b1))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (λ w1 e1 h z → h)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x) f g ez)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : A #⇛ #LT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T1 #⇛ #LT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'


typeSysConds-LT-extrevl2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T2' #⇛ #LT a1 b1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T2 #⇛ #LT a1 b1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi =
      strongMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (strongMonEq-sym (→#strongMonEq w c1 c2 c1 a1 refl (CTerm≡ (LTinj1 (⇛-val-det tt tt y₁ x))) x₄))
        (strongMonEq-sym (→#strongMonEq w d1 d2 d1 b1 refl (CTerm≡ (LTinj2 (⇛-val-det tt tt y₁ x))) x₅))
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → #lift-<NUM-pair w'' a1 b1))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w1 e1 h z → h)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x) f g ez)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : A #⇛ #LT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T2 #⇛ #LT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'



typeSysConds-LT-extrevr1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T2' #⇛ #LT a2 b2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T2 #⇛ #LT a2 b2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      strongMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (strongMonEq-trans (→#strongMonEq w a1 a2 a1 c2 refl (CTerm≡ (LTinj1 (⇛-val-det tt tt x₁ y₁))) s) (strongMonEq-sym x₄))
        (strongMonEq-trans (→#strongMonEq w b1 b2 b1 d2 refl (CTerm≡ (LTinj2 (⇛-val-det tt tt x₁ y₁))) s₁) (strongMonEq-sym x₅))
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → #lift-<NUM-pair w'' a1 b1))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (λ w1 e1 h z → h)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x₁) f g ez)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : B #⇛ #LT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T2 #⇛ #LT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'


typeSysConds-LT-extrevr2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#LT a1 b1) at w) (x₁ : B #⇛ (#LT a2 b2) at w)
                           (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                         → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #strongMonEq w' a1 a2) (s₁ : #strongMonEq w' b1 b2)
              → T1' #⇛ #LT a2 b2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → T1 #⇛ #LT a2 b2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      strongMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (→#strongMonEq w a1 a2 a1 c1 refl (CTerm≡ (LTinj1 (⇛-val-det tt tt x₁ y))) s)
        (→#strongMonEq w b1 b2 b1 d1 refl (CTerm≡ (LTinj2 (⇛-val-det tt tt x₁ y))) s₁)
        eqi
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (LTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → #lift-<NUM-pair w'' a1 b1))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w1 e1 h z → h)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (#strongMonEq-mon {a1} {a2} s w1 e1) (#strongMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x₁) f g ez)

    concl : (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
            (comp : B #⇛ #LT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
          → (comp : T1 #⇛ #LT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'


eqInType-⇛-LT : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 a b : CTerm)
                 → A #⇛ #LT a1 b1 at w
                 → B #⇛ #LT a2 b2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
eqInType-⇛-LT u w A B a1 b1 a2 b2 a b c₁ c₂ eqt eqi =
  concl c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → T1' #⇛ #LT a1 b1 at w' → T2' #⇛ #LT a2 b2 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → T1 #⇛ #LT a1 b1 at w → T2 #⇛ #LT a2 b2 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a₁ a₂ b₁ b₂ x x₁ x₂ x₃) ind c₁ c₂ a b ei =
      Mod.∀𝕎-□Func M
        (λ w1 e1 h → →#lift-<NUM-pair w1 a₁ b₁ a1 b1
                       (CTerm≡ (LTinj1 (⇛-val-det tt tt x c₁)))
                       (CTerm≡ (LTinj2 (⇛-val-det tt tt x c₁)))
                       h)
        ei
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind c₁ c₂ a b ei = ⊥-elim (LTneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind c₁ c₂ a b ei = ⊥-elim (LTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind c₁ c₂ a b ei = ⊥-elim (LTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind c₁ c₂ a b ei = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind c₁ c₂ a b ei = ⊥-elim (LTneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind c₁ c₂ a b ei = ⊥-elim (LTneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → #lift-<NUM-pair w'' a1 b1))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w1 e1 h z → h)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (c₁ : A #⇛ #LT a1 b1 at w) (c₂ : B #⇛ #LT a2 b2 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (c₁ : T1 #⇛ #LT a1 b1 at w) (c₂ : T2 #⇛ #LT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt



eqInType-⇛-LT-rev : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 a b : CTerm)
                  → A #⇛ #LT a1 b1 at w
                  → B #⇛ #LT a2 b2 at w
                  → (eqt : eqTypes u w A B)
                  → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
                  → eqInType u w eqt a b
eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ eqt ei =
  concl c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → T1' #⇛ #LT a1 b1 at w' → T2' #⇛ #LT a2 b2 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt' a₁ b₁)
          → T1 #⇛ #LT a1 b1 at w → T2 #⇛ #LT a2 b2 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (LTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a₁ a₂ b₁ b₂ x x₁ x₂ x₃) ind c₁ c₂ a b ei =
      Mod.∀𝕎-□Func M
        (λ w1 e1 h → →#lift-<NUM-pair w1 a1 b1 a₁ b₁
                       (CTerm≡ (LTinj1 (⇛-val-det tt tt c₁ x)))
                       (CTerm≡ (LTinj2 (⇛-val-det tt tt c₁ x)))
                       h)
        ei
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind c₁ c₂ a b ei = ⊥-elim (LTneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind c₁ c₂ a b ei = ⊥-elim (LTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind c₁ c₂ a b ei = ⊥-elim (LTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind c₁ c₂ a b ei = ⊥-elim (LTneqNOREAD (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA) ind c₁ c₂ a b ei = ⊥-elim (LTneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind c₁ c₂ a b ei = ⊥-elim (LTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind c₁ c₂ a b ei = ⊥-elim (LTneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind c₁ c₂ a b ei = ⊥-elim (LTneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → #lift-<NUM-pair w' a1 b1) e1)
            j = Mod.↑□ M ei e1

    concl : (c₁ : A #⇛ #LT a1 b1 at w) (c₂ : B #⇛ #LT a2 b2 at w) (a b : CTerm)
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (c₁ : T1 #⇛ #LT a1 b1 at w) (c₂ : T2 #⇛ #LT a2 b2 at w) (a b : CTerm)
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b)
        ind
        eqt



typeSysConds-LT-local : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #LT a1 b1 at w) (x₁ : B #⇛ #LT a2 b2 at w)
                        (s : #strongMonEq w a1 a2) (s₁ : #strongMonEq w b1 b2)
                        → eqInTypeLocal {u} (EQTLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-LT-local u w A B a1 b1 a2 b2 x x₁ s s₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--} → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → #lift-<NUM-pair w'' a1 b1))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
      where
        aw' : □· w1 (λ w' e → #lift-<NUM-pair w' a1 b1)
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
