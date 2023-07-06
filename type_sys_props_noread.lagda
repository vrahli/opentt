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


module type_sys_props_noread {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
--NOREADneqNAT : {a : Term} → ¬ NOREAD ≡ NAT
--NOREADneqNAT {a} ()

NOREADneqQNAT : ¬ NOREAD ≡ QNAT
NOREADneqQNAT ()

--NOREADneqTNAT : {a : Term} → ¬ NOREAD ≡ TNAT
--NOREADneqTNAT {a} ()

NOREADneqLT : {c d : Term} → ¬ NOREAD ≡ LT c d
NOREADneqLT {c} {d} ()

NOREADneqQLT : {c d : Term} → ¬ NOREAD ≡ QLT c d
NOREADneqQLT {c} {d} ()

NOREADneqFREE : ¬ NOREAD ≡ FREE
NOREADneqFREE ()

NOREADneqPI : {c : Term} {d : Term} → ¬ NOREAD ≡ PI c d
NOREADneqPI {c} {d} ()

NOREADneqW : {c d e : Term} → ¬ NOREAD ≡ WT c d e
NOREADneqW {c} {d} {e} ()

NOREADneqM : {c d e : Term} → ¬ NOREAD ≡ MT c d e
NOREADneqM {c} {d} {e} ()

NOREADneqSUM : {c : Term} {d : Term} → ¬ NOREAD ≡ SUM c d
NOREADneqSUM {c} {d} ()

NOREADneqSET : {c : Term} {d : Term} → ¬ NOREAD ≡ SET c d
NOREADneqSET {c} {d} ()

NOREADneqISECT : {c : Term} {d : Term} → ¬ NOREAD ≡ ISECT c d
NOREADneqISECT {c} {d} ()

NOREADneqTUNION : {c : Term} {d : Term} → ¬ NOREAD ≡ TUNION c d
NOREADneqTUNION {c} {d} ()

NOREADneqUNION : {c : Term} {d : Term} → ¬ NOREAD ≡ UNION c d
NOREADneqUNION {c} {d} ()

--NOREADneqQTUNION : {c : Term} {d : Term} → ¬ NOREAD ≡ QTUNION c d
--NOREADneqQTUNION {a} {c} {d} ()

NOREADneqEQ : {c d e : Term} → ¬ NOREAD ≡ EQ c d e
NOREADneqEQ {c} {d} {e} ()

NOREADneqDUM : {c : Term} → ¬ NOREAD ≡ DUM c
NOREADneqDUM {c} ()

NOREADneqFFDEFS : {c d : Term} → ¬ NOREAD ≡ FFDEFS c d
NOREADneqFFDEFS {c} {d} ()

NOREADneqLIFT : {c : Term} → ¬ NOREAD ≡ LIFT c
NOREADneqLIFT {c} ()

NOREADneqTSQUASH : {c : Term} → ¬ NOREAD ≡ TSQUASH c
NOREADneqTSQUASH {c} ()

NOREADneqNOWRITE : ¬ NOREAD ≡ NOWRITE
NOREADneqNOWRITE ()

--NOREADneqTTRUNC : {c : Term} → ¬ NOREAD ≡ TTRUNC c
--NOREADneqTTRUNC {a} {c} ()

NOREADneqSUBSING : {c : Term} → ¬ NOREAD ≡ SUBSING c
NOREADneqSUBSING {c} ()

NOREADneqPURE : ¬ NOREAD ≡ PURE
NOREADneqPURE ()

NOREADneqNOSEQ : ¬ NOREAD ≡ NOSEQ
NOREADneqNOSEQ ()

NOREADneqTERM : {c : Term} → ¬ NOREAD ≡ TERM c
NOREADneqTERM {c} ()

NOREADneqLOWER : {c : Term} → ¬ NOREAD ≡ LOWER c
NOREADneqLOWER {c} ()

NOREADneqSHRINK : {c : Term} → ¬ NOREAD ≡ SHRINK c
NOREADneqSHRINK {c} ()

NOREADneqUNIV : {n : ℕ} → ¬ NOREAD ≡ UNIV n
NOREADneqUNIV {n} ()


typeSysConds-NOREAD-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                            → eqTypes u w B A
typeSysConds-NOREAD-tsym u w A B x x₁ = EQTNOREAD x₁ x


typeSysConds-NOREAD-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                              → eqTypesTrans u w A B
typeSysConds-NOREAD-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #NOREAD at w' → T1' #⇛ #NOREAD at w'
              → eqTypes u' w' A T2')
          → A #⇛ #NOREAD at w → T1 #⇛ #NOREAD at w
          → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ = ⊥-elim (NOREADneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ = ⊥-elim (NOREADneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁ = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁
      = EQTNOREAD x y₁
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (NOREADneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁)

    concl : (c₁ : A #⇛ #NOREAD at w) (c₁ : B #⇛ #NOREAD at w)
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #NOREAD at w) (c₂ : T1 #⇛ #NOREAD at w)
           → eqTypes u w A T2)
        ind
        eqt


typeSysConds-NOREAD-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                            → eqInTypeSym u {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M (λ w e p → NOREADeq-sym {w} {f} {g} p) eqa



typeSysConds-NOREAD-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → NOREADeq w' f g
                      → NOREADeq w' g h
                      → NOREADeq w' f h)
    aw w1 e1 p₁ p₂ = NOREADeq-trans {w1} {f} {g} {h} p₁ p₂



typeSysConds-NOREAD-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → T1' #⇛ #NOREAD at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOREADeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T1 #⇛ #NOREAD at w → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta exta inda x f g eqi = {!!}
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NOREAD at w) (a b : CTerm)
            → □· w (λ w' e → NOREADeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOREAD at w) (a b : CTerm)
          → □· w (λ w' e → NOREADeq w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-NOREAD-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOREAD at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOREADeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T2 #⇛ #NOREAD at w
          → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi
      --
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NOREAD at w)
            (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOREAD at w)
          → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOREAD-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOREAD at w'
              → (a b : CTerm) →  □· w' (λ w'' e → NOREADeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T2 #⇛ #NOREAD at w
          → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NOREAD at w)
            (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOREAD at w)
          → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOREAD-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T1' #⇛ #NOREAD at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOREADeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T1 #⇛ #NOREAD at w
          → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NOREAD at w)
            (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOREAD at w)
          → (a b : CTerm) → □· w (λ w' e → NOREADeq w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOREAD-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T1' #⇛ #NOREAD at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOREADeq w'' a b))
          → T1 #⇛ #NOREAD at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOREADeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOREADeq w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func
             M (λ w e z y → z)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x) f g ez)

    concl : (comp : A #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOREADeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOREADeq w' a b))
        ind
        eqt'



typeSysConds-NOREAD-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOREAD at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOREADeq w'' a b))
          → T2 #⇛ #NOREAD at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOREADeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOREADeq w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w e z y → z)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x) f g ez)

    concl : (comp : A #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOREADeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOREADeq w' a b))
        ind
        eqt'



typeSysConds-NOREAD-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                               (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOREAD at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOREADeq w'' a b))
          → T2 #⇛ #NOREAD at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOREADeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → NOREADeq w'' f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (λ w e z y → z)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x₁) f g ez)

    concl : (comp : B #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
           → □· w (λ w' e → NOREADeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOREADeq w' a b))
        ind
        eqt'



typeSysConds-NOREAD-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                               (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOREAD x x₁)
typeSysConds-NOREAD-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T1' #⇛ #NOREAD at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOREADeq w'' a b))
          → T1 #⇛ #NOREAD at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOREADeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOREADneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOREADneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOREADneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOREADneqQTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOREADneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi = ⊥-elim (NOREADneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOREADeq w' f g
                           → NOREADeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOREADneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOREADneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOREADneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOREADeq w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w e z y → z)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x₁) f g ez)

    concl : (comp : B #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOREADeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOREAD at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOREADeq w' a b))
        ind
        eqt'




eqInType-⇛-NOREAD : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #NOREAD at w
                      → B #⇛ #NOREAD at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → NOREADeq w' a b)
eqInType-⇛-NOREAD u w A B a b c₁ c₂ eqt eqi = typeSysConds-NOREAD-extrevl1 u w A B c₁ c₂ B eqt a b eqi


eqInType-⇛-NOREAD2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #NOREAD at w
                       → B #⇛ #NOREAD at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → NOREADeq w' a b)
eqInType-⇛-NOREAD2 u w A B a b c₁ c₂ eqt ei = typeSysConds-NOREAD-extrevl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei


eqInType-⇛-NOREAD-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #NOREAD at w
                          → B #⇛ #NOREAD at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → NOREADeq w' a b)
                          → eqInType u w eqt a b
eqInType-⇛-NOREAD-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-NOREAD-extl1 u w A B c₁ c₂ B eqt a b ei


eqInType-⇛-NOREAD-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #NOREAD at w
                           → B #⇛ #NOREAD at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → NOREADeq w' a b)
                           → ≡∈Type u w eqt a b
eqInType-⇛-NOREAD-rev2 u w A B a b c₁ c₂ eqt ei = typeSysConds-NOREAD-extl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei


typeSysConds-NOREAD-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                             → eqInTypeLocal (EQTNOREAD x x₁)
typeSysConds-NOREAD-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → NOREADeq w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → NOREADeq w'' a b)
        aw' = eqInType-⇛-NOREAD u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → NOREADeq w' a b → (x₂ : w ⊑· w') → NOREADeq w' a b)
        aw'' w' e' p x₂ = p



typeSysConds-NOREAD : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #NOREAD at w) (x₁ : B #⇛ #NOREAD at w)
                       → TSP {u} (EQTNOREAD x x₁)
typeSysConds-NOREAD u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-NOREAD-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NOREAD-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTNOREAD x x₁)
    isym = typeSysConds-NOREAD-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNOREAD x x₁)
    itrans = typeSysConds-NOREAD-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextl1 = typeSysConds-NOREAD-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextl2 = typeSysConds-NOREAD-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextr1 = typeSysConds-NOREAD-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextr2 = typeSysConds-NOREAD-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextrl1 = typeSysConds-NOREAD-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextrl2 = typeSysConds-NOREAD-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextrr1 = typeSysConds-NOREAD-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOREAD x x₁)
    iextrr2 = typeSysConds-NOREAD-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTNOREAD x x₁)
    local = typeSysConds-NOREAD-local u w A B x x₁

\end{code}
