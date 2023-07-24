\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import choiceExt
open import newChoice
open import mod
open import encode

-- We add here further induction principles that can be derived from the one in ind2.lagda
-- and that are more convenient to prove properties about equalTypes and equalInType

module ind3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)


≡Types→equalTypes : {v : 𝕌} {w : 𝕎·} {T1 T2 : CTerm}
                     → ≡Types v w T1 T2
                     → equalTypes (v ·ₙ) w T1 T2
≡Types→equalTypes {(n , .(uniUpTo n)) , refl} {w} {T1} {T2} eqt = eqt -- uses K


<Type-≡Types→equalTypes : {u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} {eqt' : equalTypes u' w' T1' T2'}
                           (v : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (z : ≡Types v w T1 T2)
                           → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 (v ·ₙ)} (≡Types→equalTypes {v} z)
                           → <Type {ℕ→𝕌 u'} eqt' {v} z
<Type-≡Types→equalTypes {u'} {w'} {T1'} {T2'} {eqt'} ((n , .(uniUpTo n)) , refl) w T1 T2 z h = h -- uses K


{--
≡Types-ind : {K : Level} (P : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} → ≡Types u w T1 T2 → Set(K))
           → ({u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
               → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' {u} eqt → P {u'} eqt')
               → P {u} eqt)
           → {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2) → P eqt
≡Types-ind {K} P ind {u} {w} {T1} {T2} eqt = {!!}
--}


equalTypes-ind : {L : Level} (P : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) → Set(L))
                 → ({u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
                       → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2')
                              → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → P {u'} eqt')
                       → P {u} eqt)
                 → {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) → P eqt
equalTypes-ind {L} P ind {u} {w0} {X1} {X2} eqt =
  ind<Type
    (λ {v} {w} {T1} {T2} z → P {v ·ₙ} {w} {T1} {T2} (≡Types→equalTypes {v} z))
    (λ {v} {w} {T1} {T2} z q →
      ind {v ·ₙ} {w} {T1} {T2} (≡Types→equalTypes z)
          (λ {u'} {w'} {T1'} {T2'} eqt' h → q {ℕ→𝕌 u'} {w'} {T1'} {T2'} eqt' (<Type-≡Types→equalTypes v w T1 T2 z h)))
    eqt


equalTerms-ind : {K : Level} (P : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b) → Set(K))
                 → ({u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
                       → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                              → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → P {u'} eqt' eqi')
                       → P {u} eqt eqi)
                 → {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
                    (a b : CTerm) (eqi : equalTerms u w eqt a b) → P eqt eqi
equalTerms-ind {K} P ind {u} {w0} {X1} {X2} eqt =
  equalTypes-ind {lsuc L ⊔ K}
    (λ {u} {w} {T1} {T2} eqt → (a b : CTerm) (e : equalTerms u w eqt a b) → P eqt e)
    (λ {u} {w} {T1} {T2} eqt q a b eqi →
      ind {u} {w} {T1} {T2} eqt {a} {b} eqi
          (λ {u'} {w'} {T1'} {T2'} eqt' {a'} {b'} eqi' z → q eqt' z a' b' eqi'))
    eqt



-- Testing equalTyes-ind
-- & we might need that for equalInType-ind
-- we'll need the type system properties for that.
-- We'll state this principle below later
{--
equalTypes-refl : (u : ℕ) (w : 𝕎·) (T1 T2 : CTerm)
                   → equalTypes u w T1 T2
                   → equalTypes u w T1 T1
equalTypes-refl u w T1 T2 eqt =
  equalTypes-ind
    (λ {u} {w} {T1} {T2} eqt → equalTypes u w T1 T1)
    ind
    eqt
  where
    ind : {u : ℕ} {w : 𝕎·} {T1 : CTerm} {T2 : CTerm} (eqt : equalTypes u w T1 T2)
          → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2')
                 → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → equalTypes u' w' T1' T1')
          → equalTypes u w T1 T1
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ih = EQTNAT x x
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ih = EQTQNAT x x
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ih = EQTTNAT x x
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ih = EQTLT a1 a1 b1 b1 x x (strongMonEq-refl x₂) (strongMonEq-refl x₃)
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ih = EQTQLT a1 a1 b1 b1 x x (weakMonEq-refl x₂) (weakMonEq-refl x₃)
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ih = EQTFREE x x
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ih =
      EQTPI
        A1 B1 A1 B1 x x
        (λ w1 e1 → ih {u} {w1} {A1} {A2} (eqta w1 e1) (<Type1 {ℕ→𝕌 u} (eqta w1 e1) {ℕ→𝕌 u} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypePIa (ℕ→𝕌 u) w T1 T2 A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1 )))
        (λ w1 e1 a1 a2 a∈ → {!ih {u} {w1} {sub0 a1 B1} {sub0 a2 B2} (eqtb w1 e1 a1 a2 ?)!})
        {!!}
        {!!}
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTNOWRITE A1 A2 x x₁ eqtA exta) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ih = {!!}
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ih = EQTPURE x x
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ih = EQTNOSEQ x x
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ih = EQTNOENC x x
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ih = {!!}
    ind {u} {w} {T1} {T2} (EQTBAR x) ih = EQTBAR (Mod.∀𝕎-□Func M (λ w1 e1 z → ih {u} {w1} {T1} {T2} z (<Type1 {ℕ→𝕌 u} z {ℕ→𝕌 u} (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z))) x)
--}


{--
equalInType-ind : {K : Level} (P : {u : ℕ} {w : 𝕎·} {T : CTerm} {a b : CTerm} (eqi : equalInType u w T a b) → Set(K))
                 → ({u : ℕ} {w : 𝕎·} {T : CTerm} {a b : CTerm} (eqi : equalInType u w T a b)
                       → ({u' : ℕ} {w' : 𝕎·} {T' : CTerm} {a' b' : CTerm} (eqi' : equalInType u' w' T' a' b')
                              → <Type {ℕ→𝕌 u'} (fst eqi') {ℕ→𝕌 u} (fst eqi) → P {u'} eqi')
                       → P {u} eqi)
                 → {u : ℕ} {w : 𝕎·} {T : CTerm} (a b : CTerm) (eqi : equalInType u w T a b) → P eqi
equalInType-ind {K} P ind {u} {w0} {X} a b (eqt , eqi) =
  equalTerms-ind {K}
    (λ {u} {w} {T1} {T2} eqt {a} {b} eqi → {!!})
    {!!}
    eqt a b eqi
--}
{--
  equalTerms-ind {K}
    (λ {u} {w} {T1} {T2} eqt {a} {b} eqi → P {u} {w} {T1} {a} {b} ?)
    {!!}
    {!!} {!!} {!!}
--}

\end{code}
