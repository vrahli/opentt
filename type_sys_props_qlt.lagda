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


module type_sys_props_qlt {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--QLTneqNAT : {u v : Term} → ¬ QLT u v ≡ NAT
--QLTneqNAT {u} {v} ()

QLTneqQNAT : {u v : Term} → ¬ QLT u v ≡ QNAT
QLTneqQNAT {u} {v} ()

--QLTneqTNAT : {u v : Term} → ¬ QLT u v ≡ TNAT
--QLTneqTNAT {u} {v} ()

QLTneqLT : {u v : Term} {c d : Term} → ¬ QLT u v ≡ LT c d
QLTneqLT {u} {v} {c} {d} ()

QLTneqFREE : {u v : Term} → ¬ QLT u v ≡ FREE
QLTneqFREE {u} {v} ()

QLTneqPI : {u v : Term} {c d : Term} → ¬ QLT u v ≡ PI c d
QLTneqPI {u} {v} {c} {d} ()

QLTneqW : {u v : Term} {c d e : Term} → ¬ QLT u v ≡ WT c d e
QLTneqW {u} {v} {c} {d} {e} ()

QLTneqM : {u v : Term} {c d e : Term} → ¬ QLT u v ≡ MT c d e
QLTneqM {u} {v} {c} {d} {e} ()

QLTneqSUM : {u v : Term} {c d : Term} → ¬ QLT u v ≡ SUM c d
QLTneqSUM {u} {v} {c} {d} ()

QLTneqSET : {u v : Term} {c d : Term} → ¬ QLT u v ≡ SET c d
QLTneqSET {u} {v} {c} {d} ()

QLTneqTUNION : {u v : Term} {c d : Term} → ¬ QLT u v ≡ TUNION c d
QLTneqTUNION {u} {v} {c} {d} ()

QLTneqUNION : {u v : Term} {c d : Term} → ¬ QLT u v ≡ UNION c d
QLTneqUNION {u} {v} {c} {d} ()

QLTneqISECT : {u v : Term} {c d : Term} → ¬ QLT u v ≡ ISECT c d
QLTneqISECT {u} {v} {c} {d} ()

--QLTneqQTUNION : {u v : Term} {c d : Term} → ¬ QLT u v ≡ QTUNION c d
--QLTneqQTUNION {u} {v} {c} {d} ()

QLTneqEQ : {u v : Term} {c d e : Term} → ¬ QLT u v ≡ EQ c d e
QLTneqEQ {u} {v} {c} {d} {e} ()

--QLTneqTSQUASH : {u v : Term} {c : Term} → ¬ QLT u v ≡ TSQUASH c
--QLTneqTSQUASH {u} {v} {c} ()

--QLTneqTTRUNC : {u v : Term} {c : Term} → ¬ QLT u v ≡ TTRUNC c
--QLTneqTTRUNC {u} {v} {c} ()

QLTneqNOWRITE : {u v : Term} → ¬ QLT u v ≡ NOWRITE
QLTneqNOWRITE {u} {v} ()

QLTneqNOREAD : {u v : Term} → ¬ QLT u v ≡ NOREAD
QLTneqNOREAD {u} {v} ()

QLTneqSUBSING : {u v : Term} {c : Term} → ¬ QLT u v ≡ SUBSING c
QLTneqSUBSING {u} {v} {c} ()

QLTneqPURE : {u v : Term} → ¬ QLT u v ≡ PURE
QLTneqPURE {u} {v} ()

QLTneqNOSEQ : {u v : Term} → ¬ QLT u v ≡ NOSEQ
QLTneqNOSEQ {u} {v} ()

QLTneqNOENC : {u v : Term} → ¬ QLT u v ≡ NOENC
QLTneqNOENC {u} {v} ()

QLTneqTERM : {u v c : Term} → ¬ QLT u v ≡ TERM c
QLTneqTERM {u} {v} {c} ()

--QLTneqLIFT : {u v : Term} {c : Term} → ¬ QLT u v ≡ LIFT c
--QLTneqLIFT {u} {v} {c} ()

QLTneqPARTIAL : {u v : Term} {c : Term} → ¬ QLT u v ≡ PARTIAL c
QLTneqPARTIAL {u} {v} {c} ()

QLTneqFFDEFS : {u v : Term} {c d : Term} → ¬ QLT u v ≡ FFDEFS c d
QLTneqFFDEFS {u} {v} {c} {d} ()

QLTneqLOWER : {u v : Term} {c : Term} → ¬ QLT u v ≡ LOWER c
QLTneqLOWER {u} {v} {c} ()

QLTneqSHRINK : {u v : Term} {c : Term} → ¬ QLT u v ≡ SHRINK c
QLTneqSHRINK {u} {v} {c} ()

QLTneqUNIV : {u v : Term} {n : ℕ} → ¬ QLT u v ≡ UNIV n
QLTneqUNIV {u} {v} {n} ()


→#weakMonEq : (w : 𝕎·) (a1 a2 b1 b2 : CTerm)
            → a1 ≡ b1
            → a2 ≡ b2
            → #weakMonEq w a1 a2
            → #weakMonEq w b1 b2
→#weakMonEq w a1 a2 b1 b2 refl refl s = s


→#lift-<NUM-pair : (w : 𝕎·) (a1 a2 b1 b2 : CTerm)
                 → a1 ≡ b1
                 → a2 ≡ b2
                 → #lift-<NUM-pair w a1 a2
                 → #lift-<NUM-pair w b1 b2
→#lift-<NUM-pair w a1 a2 b1 b2 refl refl s = s


typeSysConds-QLT-ttrans : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                         (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqTypesTrans u w A B
typeSysConds-QLT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt = concl x x₁ s s₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #QLT a1 b1 at w' → T1' #⇛ #QLT a2 b2 at w'
              → #weakMonEq w' a1 a2
              → #weakMonEq w' b1 b2
              → eqTypes u' w' A T2')
          → A #⇛ #QLT a1 b1 at w → T1 #⇛ #QLT a2 b2 at w
          → #weakMonEq w a1 a2
          → #weakMonEq w b1 b2
          → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ s s₁ = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ s s₁ =
      EQTQLT a1 c2 b1 d2 x y₁
        (weakMonEq-trans s  (→#weakMonEq w c1 c2 a2 c2 (CTerm≡ (QLTinj1 (⇛-val-det tt tt y x₁))) refl x₄))
        (weakMonEq-trans s₁ (→#weakMonEq w d1 d2 b2 d2 (CTerm≡ (QLTinj2 (⇛-val-det tt tt y x₁))) refl x₅))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ s s₁ = ⊥-elim (QLTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ s s₁ = ⊥-elim (QLTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ s s₁ = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ s s₁ = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ s s₁ = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ s s₁ = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ s s₁ = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁ s s₁ = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ s s₁ = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ s s₁ = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ s s₁ = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ s s₁ =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁) (#weakMonEq-mon {a1} {a2} s w' e') (#weakMonEq-mon {b1} {b2} s₁ w' e')

    concl : (c₁ : A #⇛ #QLT a1 b1 at w) (c₁ : B #⇛ #QLT a2 b2 at w)
          → #weakMonEq w a1 a2
          → #weakMonEq w b1 b2
          → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #QLT a1 b1 at w) (c₂ : T1 #⇛ #QLT a2 b2 at w)
           → #weakMonEq w a1 a2
           → #weakMonEq w b1 b2
           → eqTypes u w A T2)
        ind
        eqt



typeSysConds-QLT-extl1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                        (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                      → eqInTypeExtL1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl x s s₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → T1' #⇛ #QLT a1 b1 at w'
              → #weakMonEq w' a1 a2
              → #weakMonEq w' b1 b2
              → (a b : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → T1 #⇛ #QLT a1 b1 at w
          → #weakMonEq w a1 a2
          → #weakMonEq w b1 b2
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x s s₁ f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x s s₁ f g eqi =
      Mod.∀𝕎-□Func M
        (λ w1 e1 q → →#lift-<NUM-pair w1 a1 b1 c1 d1 (CTerm≡ (QLTinj1 (⇛-val-det tt tt x y))) (CTerm≡ (QLTinj2 (⇛-val-det tt tt x y))) q)
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x s s₁ f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x s s₁ f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x s s₁ f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x s s₁ f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x s s₁ f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x s s₁ f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x s s₁ f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x s s₁ f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x s s₁ f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x s s₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
             (⇛-mon e1 x) (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1) f g
             (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #QLT a1 b1 at w)
            (s₁ : #weakMonEq w a1 a2)
            (s₂ : #weakMonEq w b1 b2)
            → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #QLT a1 b1 at w)
          → #weakMonEq w a1 a2
          → #weakMonEq w b1 b2
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QLT-extl2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                          (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                          → eqInTypeExtL2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T2' #⇛ #QLT a1 b1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T2 #⇛ #QLT a1 b1 at w
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi =
      weakMonEq-preserves-□· {_} {a1} {b1} {c1} {d1}
        (→#weakMonEq w c1 c2 c1 a1 refl (CTerm≡ (QLTinj1 (⇛-val-det tt tt y₁ x))) x₄)
        (→#weakMonEq w d1 d2 d1 b1 refl (CTerm≡ (QLTinj2 (⇛-val-det tt tt y₁ x))) x₅)
        eqi --⊥-elim (QLTneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x y₁))
{--      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                            → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
        aw w1 e1 p
          rewrite sym (#ISECTinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#ISECTinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
            ISECTeq-ext-eq {_} {_} {_} {_} {f} {g} (TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1)) p--}
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : A #⇛ #QLT a1 b1 at w)
            (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T2 #⇛ #QLT a1 b1 at w)
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QLT-extr1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                        (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                      → eqInTypeExtR1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T2' #⇛ #QLT a2 b2 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T2 #⇛ #QLT a2 b2 at w
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      weakMonEq-preserves-□· {_} {a1} {b1} {c1} {d1}
        (weakMonEq-trans x₄ (weakMonEq-sym (→#weakMonEq w a1 a2 a1 c2 refl (CTerm≡ (QLTinj1 (⇛-val-det tt tt x₁ y₁))) s)))
        (weakMonEq-trans x₅ (weakMonEq-sym (→#weakMonEq w b1 b2 b1 d2 refl (CTerm≡ (QLTinj2 (⇛-val-det tt tt x₁ y₁))) s₁)))
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : B #⇛ #QLT a2 b2 at w)
            (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T2 #⇛ #QLT a2 b2 at w)
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QLT-extr2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                        (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                      → eqInTypeExtR2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T1' #⇛ #QLT a2 b2 at w'
              → (a b : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt'' a b)
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T1 #⇛ #QLT a2 b2 at w
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      weakMonEq-preserves-□· {_} {a1} {b1} {c1} {d1}
        (weakMonEq-sym (→#weakMonEq w a1 a2 a1 c1 refl (CTerm≡ (QLTinj1 (⇛-val-det tt tt x₁ y))) s))
        (weakMonEq-sym (→#weakMonEq w b1 b2 b1 d1 refl (CTerm≡ (QLTinj2 (⇛-val-det tt tt x₁ y))) s₁))
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind s s₁ x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : B #⇛ #QLT a2 b2 at w)
            (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T1 #⇛ #QLT a2 b2 at w)
          → (a b : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-QLT-extrevl1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                           → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T1' #⇛ #QLT a1 b1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T1 #⇛ #QLT a1 b1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi =
      weakMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (→#weakMonEq w c1 c1 a1 c1 (CTerm≡ (QLTinj1 (⇛-val-det tt tt y x))) refl (weakMonEq-refl x₄))
        (→#weakMonEq w d1 d1 b1 d1 (CTerm≡ (QLTinj2 (⇛-val-det tt tt y x))) refl (weakMonEq-refl x₅))
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x y))
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
               (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x) f g ez)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : A #⇛ #QLT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T1 #⇛ #QLT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'


typeSysConds-QLT-extrevl2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T2' #⇛ #QLT a1 b1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T2 #⇛ #QLT a1 b1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x f g eqi =
      weakMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (weakMonEq-sym (→#weakMonEq w c1 c2 c1 a1 refl (CTerm≡ (QLTinj1 (⇛-val-det tt tt y₁ x))) x₄))
        (weakMonEq-sym (→#weakMonEq w d1 d2 d1 b1 refl (CTerm≡ (QLTinj2 (⇛-val-det tt tt y₁ x))) x₅))
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x y₁))
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
               (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x) f g ez)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : A #⇛ #QLT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T2 #⇛ #QLT a1 b1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'



typeSysConds-QLT-extrevr1 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T2' #⇛ #QLT a2 b2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T2 #⇛ #QLT a2 b2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      weakMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (weakMonEq-trans (→#weakMonEq w a1 a2 a1 c2 refl (CTerm≡ (QLTinj1 (⇛-val-det tt tt x₁ y₁))) s) (weakMonEq-sym x₄))
        (weakMonEq-trans (→#weakMonEq w b1 b2 b1 d2 refl (CTerm≡ (QLTinj2 (⇛-val-det tt tt x₁ y₁))) s₁) (weakMonEq-sym x₅))
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x₁ y₁))
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
               (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x₁) f g ez)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : B #⇛ #QLT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T2 #⇛ #QLT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'


typeSysConds-QLT-extrevr2 : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁ C eqt' =
  concl s s₁ x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (s : #weakMonEq w' a1 a2) (s₁ : #weakMonEq w' b1 b2)
              → T1' #⇛ #QLT a2 b2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → T1 #⇛ #QLT a2 b2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind s s₁ x₁ f g eqi =
      weakMonEq-preserves-□· {_} {c1} {d1} {a1} {b1}
        (→#weakMonEq w a1 a2 a1 c1 refl (CTerm≡ (QLTinj1 (⇛-val-det tt tt x₁ y))) s)
        (→#weakMonEq w b1 b2 b1 d1 refl (CTerm≡ (QLTinj2 (⇛-val-det tt tt x₁ y))) s₁)
        eqi
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind s s₁ x₁ f g eqi = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt x₁ y))
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
               (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
               (⇛-mon e1 x₁) f g ez)

    concl : (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
            (comp : B #⇛ #QLT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
          → (comp : T1 #⇛ #QLT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt'


eqInType-⇛-QLT : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 a b : CTerm)
                 → A #⇛ #QLT a1 b1 at w
                 → B #⇛ #QLT a2 b2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
eqInType-⇛-QLT u w A B a1 b1 a2 b2 a b c₁ c₂ eqt eqi =
  concl c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → T1' #⇛ #QLT a1 b1 at w' → T2' #⇛ #QLT a2 b2 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1))
          → T1 #⇛ #QLT a1 b1 at w → T2 #⇛ #QLT a2 b2 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a₁ a₂ b₁ b₂ x x₁ x₂ x₃) ind c₁ c₂ a b ei = ⊥-elim (QLTneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a₁ a₂ b₁ b₂ x x₁ x₂ x₃) ind c₁ c₂ a b ei =
      Mod.∀𝕎-□Func M
        (λ w1 e1 h → →#lift-<NUM-pair w1 a₁ b₁ a1 b1
                       (CTerm≡ (QLTinj1 (⇛-val-det tt tt x c₁)))
                       (CTerm≡ (QLTinj2 (⇛-val-det tt tt x c₁)))
                       h)
        ei
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind c₁ c₂ a b ei = ⊥-elim (QLTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind c₁ c₂ a b ei = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind c₁ c₂ a b ei = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind c₁ c₂ a b ei = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt c₁ x))
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

    concl : (c₁ : A #⇛ #QLT a1 b1 at w) (c₂ : B #⇛ #QLT a2 b2 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (c₁ : T1 #⇛ #QLT a1 b1 at w) (c₂ : T2 #⇛ #QLT a2 b2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1))
        ind
        eqt



eqInType-⇛-QLT-rev : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 a b : CTerm)
                  → A #⇛ #QLT a1 b1 at w
                  → B #⇛ #QLT a2 b2 at w
                  → (eqt : eqTypes u w A B)
                  → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
                  → eqInType u w eqt a b
eqInType-⇛-QLT-rev u w A B a1 b1 a2 b2 a b c₁ c₂ eqt ei =
  concl c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → T1' #⇛ #QLT a1 b1 at w' → T2' #⇛ #QLT a2 b2 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
              → eqInType u' w' eqt' a₁ b₁)
          → T1 #⇛ #QLT a1 b1 at w → T2 #⇛ #QLT a2 b2 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (QLTneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a₁ a₂ b₁ b₂ x x₁ x₂ x₃) ind c₁ c₂ a b ei = ⊥-elim (QLTneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a₁ a₂ b₁ b₂ x x₁ x₂ x₃) ind c₁ c₂ a b ei =
      Mod.∀𝕎-□Func M
        (λ w1 e1 h → →#lift-<NUM-pair w1 a1 b1 a₁ b₁
                       (CTerm≡ (QLTinj1 (⇛-val-det tt tt c₁ x)))
                       (CTerm≡ (QLTinj2 (⇛-val-det tt tt c₁ x)))
                       h)
        ei
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind c₁ c₂ a b ei = ⊥-elim (QLTneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind c₁ c₂ a b ei = ⊥-elim (QLTneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind c₁ c₂ a b ei = ⊥-elim (QLTneqNOREAD (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA) ind c₁ c₂ a b ei = ⊥-elim (QLTneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind c₁ c₂ a b ei = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind c₁ c₂ a b ei = ⊥-elim (QLTneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind c₁ c₂ a b ei = ⊥-elim (QLTneqLIFT (⇛-val-det tt tt c₁ x))
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

    concl : (c₁ : A #⇛ #QLT a1 b1 at w) (c₂ : B #⇛ #QLT a2 b2 at w) (a b : CTerm)
            → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (c₁ : T1 #⇛ #QLT a1 b1 at w) (c₂ : T2 #⇛ #QLT a2 b2 at w) (a b : CTerm)
          → □· w (λ w' e → #lift-<NUM-pair w' a1 b1)
          → eqInType u w eqt a b)
        ind
        eqt



typeSysConds-QLT-local : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                        (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                        → eqInTypeLocal {u} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-local u w A B a1 b1 a2 b2 x x₁ s s₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--} → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → #lift-<NUM-pair w'' a1 b1))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
      where
        aw' : □· w1 (λ w' e → #lift-<NUM-pair w' a1 b1)
        aw' = eqInType-⇛-QLT u w1 A B a1 b1 a2 b2 a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-QLT : (u : univs) (w : 𝕎·) (A B a1 b1 a2 b2 : CTerm)
                  (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                  (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                  → TSP {u} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT u w A B a1 b1 a2 b2 x x₁ s s₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTQLT a2 a1 b2 b1 x₁ x (weakMonEq-sym s) (weakMonEq-sym s₁)

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-QLT-ttrans u w A B a1 b1 a2 b2 x x₁ s s₁

    isym : eqInTypeSym u {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    isym a b eqi = eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    itrans a b c eqi₁ eqi₂ = eqi₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextl1 = typeSysConds-QLT-extl1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextl2 = typeSysConds-QLT-extl2 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextr1 = typeSysConds-QLT-extr1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextr2 = typeSysConds-QLT-extr2 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrl1 = typeSysConds-QLT-extrevl1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrl2 = typeSysConds-QLT-extrevl2 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrr1 = typeSysConds-QLT-extrevr1 u w A B a1 b1 a2 b2 x x₁ s s₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrr2 = typeSysConds-QLT-extrevr2 u w A B a1 b1 a2 b2 x x₁ s s₁

    local : eqInTypeLocal (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    local = typeSysConds-QLT-local u w A B a1 b1 a2 b2 x x₁ s s₁
\end{code}
