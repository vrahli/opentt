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


module type_sys_props_nowrite {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--NOWRITEneqNAT : {a : Term} → ¬ NOWRITE ≡ NAT
--NOWRITEneqNAT {a} ()

NOWRITEneqQNAT : ¬ NOWRITE ≡ QNAT
NOWRITEneqQNAT ()

--NOWRITEneqTNAT : {a : Term} → ¬ NOWRITE ≡ TNAT
--NOWRITEneqTNAT {a} ()

NOWRITEneqLT : {c d : Term} → ¬ NOWRITE ≡ LT c d
NOWRITEneqLT {c} {d} ()

NOWRITEneqQLT : {c d : Term} → ¬ NOWRITE ≡ QLT c d
NOWRITEneqQLT {c} {d} ()

NOWRITEneqFREE : ¬ NOWRITE ≡ FREE
NOWRITEneqFREE ()

NOWRITEneqPI : {c : Term} {d : Term} → ¬ NOWRITE ≡ PI c d
NOWRITEneqPI {c} {d} ()

NOWRITEneqW : {c d e : Term} → ¬ NOWRITE ≡ WT c d e
NOWRITEneqW {c} {d} {e} ()

NOWRITEneqM : {c d e : Term} → ¬ NOWRITE ≡ MT c d e
NOWRITEneqM {c} {d} {e} ()

NOWRITEneqSUM : {c : Term} {d : Term} → ¬ NOWRITE ≡ SUM c d
NOWRITEneqSUM {c} {d} ()

NOWRITEneqSET : {c : Term} {d : Term} → ¬ NOWRITE ≡ SET c d
NOWRITEneqSET {c} {d} ()

NOWRITEneqISECT : {c : Term} {d : Term} → ¬ NOWRITE ≡ ISECT c d
NOWRITEneqISECT {c} {d} ()

NOWRITEneqTUNION : {c : Term} {d : Term} → ¬ NOWRITE ≡ TUNION c d
NOWRITEneqTUNION {c} {d} ()

NOWRITEneqUNION : {c : Term} {d : Term} → ¬ NOWRITE ≡ UNION c d
NOWRITEneqUNION {c} {d} ()

--NOWRITEneqQTUNION : {c : Term} {d : Term} → ¬ NOWRITE ≡ QTUNION c d
--NOWRITEneqQTUNION {a} {c} {d} ()

NOWRITEneqEQ : {c d e : Term} → ¬ NOWRITE ≡ EQ c d e
NOWRITEneqEQ {c} {d} {e} ()

NOWRITEneqPARTIAL : {c : Term} → ¬ NOWRITE ≡ PARTIAL c
NOWRITEneqPARTIAL {c} ()

NOWRITEneqFFDEFS : {c d : Term} → ¬ NOWRITE ≡ FFDEFS c d
NOWRITEneqFFDEFS {c} {d} ()

--NOWRITEneqLIFT : {c : Term} → ¬ NOWRITE ≡ LIFT c
--NOWRITEneqLIFT {c} ()

--NOWRITEneqTSQUASH : {c : Term} → ¬ NOWRITE ≡ TSQUASH c
--NOWRITEneqTSQUASH {c} ()

NOWRITEneqNOREAD : ¬ NOWRITE ≡ NOREAD
NOWRITEneqNOREAD ()

--NOWRITEneqTTRUNC : {c : Term} → ¬ NOWRITE ≡ TTRUNC c
--NOWRITEneqTTRUNC {a} {c} ()

NOWRITEneqSUBSING : {c : Term} → ¬ NOWRITE ≡ SUBSING c
NOWRITEneqSUBSING {c} ()

NOWRITEneqPURE : ¬ NOWRITE ≡ PURE
NOWRITEneqPURE ()

NOWRITEneqNOSEQ : ¬ NOWRITE ≡ NOSEQ
NOWRITEneqNOSEQ ()

NOWRITEneqNOENC : ¬ NOWRITE ≡ NOENC
NOWRITEneqNOENC ()

NOWRITEneqTERM : {c : Term} → ¬ NOWRITE ≡ TERM c
NOWRITEneqTERM {c} ()

NOWRITEneqLOWER : {c : Term} → ¬ NOWRITE ≡ LOWER c
NOWRITEneqLOWER {c} ()

NOWRITEneqSHRINK : {c : Term} → ¬ NOWRITE ≡ SHRINK c
NOWRITEneqSHRINK {c} ()

NOWRITEneqUNIV : {n : ℕ} → ¬ NOWRITE ≡ UNIV n
NOWRITEneqUNIV {n} ()


typeSysConds-NOWRITE-tsym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                            → eqTypes u w B A
typeSysConds-NOWRITE-tsym u w A B x x₁ = EQTNOWRITE x₁ x


typeSysConds-NOWRITE-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                              → eqTypesTrans u w A B
typeSysConds-NOWRITE-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #NOWRITE at w' → T1' #⇛ #NOWRITE at w'
              → eqTypes u' w' A T2')
          → A #⇛ #NOWRITE at w → T1 #⇛ #NOWRITE at w
          → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x x₁ = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁
      = EQTNOWRITE x y₁
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁ = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA) = ⊥-elim (NOWRITEneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁)

    concl : (c₁ : A #⇛ #NOWRITE at w) (c₁ : B #⇛ #NOWRITE at w)
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #NOWRITE at w) (c₂ : T1 #⇛ #NOWRITE at w)
           → eqTypes u w A T2)
        ind
        eqt


typeSysConds-NOWRITE-isym : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                            → eqInTypeSym u {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-isym u w A B x x₁ f g eqa =
  Mod.∀𝕎-□Func M (λ w e p → NOWRITEeq-sym {w} {f} {g} p) eqa



typeSysConds-NOWRITE-itrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                              (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                              → eqInTypeTrans u {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-itrans u w A B x x₁ f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → NOWRITEeq w' f g
                      → NOWRITEeq w' g h
                      → NOWRITEeq w' f h)
    aw w1 e1 p₁ p₂ = NOWRITEeq-trans {w1} {f} {g} {h} p₁ p₂



typeSysConds-NOWRITE-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → T1' #⇛ #NOWRITE at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOWRITEeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T1 #⇛ #NOWRITE at w → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta exta inda x f g eqi = {!!}
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta exta inda x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NOWRITE at w) (a b : CTerm)
            → □· w (λ w' e → NOWRITEeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOWRITE at w) (a b : CTerm)
          → □· w (λ w' e → NOWRITEeq w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-NOWRITE-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOWRITE at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOWRITEeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T2 #⇛ #NOWRITE at w
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi
      --
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NOWRITE at w)
            (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOWRITE at w)
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOWRITE-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOWRITE at w'
              → (a b : CTerm) →  □· w' (λ w'' e → NOWRITEeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T2 #⇛ #NOWRITE at w
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NOWRITE at w)
            (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOWRITE at w)
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOWRITE-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T1' #⇛ #NOWRITE at w'
              → (a b : CTerm) → □· w' (λ w'' e → NOWRITEeq w'' a b)
              → eqInType u' w' eqt'' a b)
          → T1 #⇛ #NOWRITE at w
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NOWRITE at w)
            (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOWRITE at w)
          → (a b : CTerm) → □· w (λ w' e → NOWRITEeq w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NOWRITE-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T1' #⇛ #NOWRITE at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq w'' a b))
          → T1 #⇛ #NOWRITE at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func
             M (λ w e z y → z)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x) f g ez)

    concl : (comp : A #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOWRITEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq w' a b))
        ind
        eqt'



typeSysConds-NOWRITE-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                                (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOWRITE at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq w'' a b))
          → T2 #⇛ #NOWRITE at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w e z y → z)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x) f g ez)

    concl : (comp : A #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → NOWRITEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq w' a b))
        ind
        eqt'



typeSysConds-NOWRITE-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                               (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T2' #⇛ #NOWRITE at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq w'' a b))
          → T2 #⇛ #NOWRITE at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq w'' f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (λ w e z y → z)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x₁) f g ez)

    concl : (comp : B #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
           → □· w (λ w' e → NOWRITEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T2 #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq w' a b))
        ind
        eqt'



typeSysConds-NOWRITE-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                               (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → T1' #⇛ #NOWRITE at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → NOWRITEeq w'' a b))
          → T1 #⇛ #NOWRITE at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → NOWRITEeq w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' f g
                           → NOWRITEeq w' f g)
        aw w1 e1 p = p
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x₁ f g eqi = ⊥-elim (NOWRITEneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x₁ f g eqi = ⊥-elim (NOWRITEneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x₁ f g eqi = ⊥-elim (NOWRITEneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x₁ f g eqi = ⊥-elim (NOWRITEneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → NOWRITEeq w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (λ w e z y → z)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (⇛-mon e1 x₁) f g ez)

    concl : (comp : B #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (comp : T1 #⇛ #NOWRITE at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → NOWRITEeq w' a b))
        ind
        eqt'




eqInType-⇛-NOWRITE : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #NOWRITE at w
                      → B #⇛ #NOWRITE at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → NOWRITEeq w' a b)
eqInType-⇛-NOWRITE u w A B a b c₁ c₂ eqt eqi = typeSysConds-NOWRITE-extrevl1 u w A B c₁ c₂ B eqt a b eqi


eqInType-⇛-NOWRITE2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                       → A #⇛ #NOWRITE at w
                       → B #⇛ #NOWRITE at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → □· w (λ w' e → NOWRITEeq w' a b)
eqInType-⇛-NOWRITE2 u w A B a b c₁ c₂ eqt ei = typeSysConds-NOWRITE-extrevl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei


eqInType-⇛-NOWRITE-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                          → A #⇛ #NOWRITE at w
                          → B #⇛ #NOWRITE at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → NOWRITEeq w' a b)
                          → eqInType u w eqt a b
eqInType-⇛-NOWRITE-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-NOWRITE-extl1 u w A B c₁ c₂ B eqt a b ei


eqInType-⇛-NOWRITE-rev2 : (u : 𝕌) (w : 𝕎·) (A B a b : CTerm)
                           → A #⇛ #NOWRITE at w
                           → B #⇛ #NOWRITE at w
                           → (eqt : ≡Types u w A B)
                           → □· w (λ w' e → NOWRITEeq w' a b)
                           → ≡∈Type u w eqt a b
eqInType-⇛-NOWRITE-rev2 u w A B a b c₁ c₂ eqt ei = typeSysConds-NOWRITE-extl1 (u ·ᵤ) w A B c₁ c₂ B eqt a b ei


typeSysConds-NOWRITE-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                             (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                             → eqInTypeLocal (EQTNOWRITE x x₁)
typeSysConds-NOWRITE-local u w A B x x₁ a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → NOWRITEeq w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → NOWRITEeq w'' a b)
        aw' = eqInType-⇛-NOWRITE u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → NOWRITEeq w' a b → (x₂ : w ⊑· w') → NOWRITEeq w' a b)
        aw'' w' e' p x₂ = p



typeSysConds-NOWRITE : (u : univs) (w : 𝕎·) (A B : CTerm)
                       (x : A #⇛ #NOWRITE at w) (x₁ : B #⇛ #NOWRITE at w)
                       → TSP {u} (EQTNOWRITE x x₁)
typeSysConds-NOWRITE u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-NOWRITE-tsym u w A B x x₁

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NOWRITE-ttrans u w A B x x₁

    isym : eqInTypeSym u {_} {A} {B} (EQTNOWRITE x x₁)
    isym = typeSysConds-NOWRITE-isym u w A B x x₁

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNOWRITE x x₁)
    itrans = typeSysConds-NOWRITE-itrans u w A B x x₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextl1 = typeSysConds-NOWRITE-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextl2 = typeSysConds-NOWRITE-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextr1 = typeSysConds-NOWRITE-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextr2 = typeSysConds-NOWRITE-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextrl1 = typeSysConds-NOWRITE-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextrl2 = typeSysConds-NOWRITE-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextrr1 = typeSysConds-NOWRITE-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNOWRITE x x₁)
    iextrr2 = typeSysConds-NOWRITE-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTNOWRITE x x₁)
    local = typeSysConds-NOWRITE-local u w A B x x₁

\end{code}
