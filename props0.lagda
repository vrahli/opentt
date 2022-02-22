\begin{code}
{-# OPTIONS --rewriting #-}

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
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import progress
open import getChoice
open import mod

module props0 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where
       --(bar : Bar W) where
open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]
impliesEqTypes : (u : ℕ) {w : 𝕎·} {A B : CTerm} → equalTypes u w A B → eqtypes w A B
impliesEqTypes u e = (u , e)

impliesEqInType : (u : ℕ) {w : 𝕎·} {T a b : CTerm} → equalInType u w T a b → eqintype w T a b
impliesEqInType u f = (u , f)

univ□· : (n : ℕ) (w : 𝕎·) → eqUnivi n w (#UNIV n) (#UNIV n)
univ□· n w =  Mod.∀𝕎-□ M λ w1 e1 → compAllRefl (UNIV n) w1 , compAllRefl (UNIV n) w1

lemma1 : (w : 𝕎·) → equalTypes 1 w (#UNIV 0) (#UNIV 0)
lemma1 w = EQTUNIV 0 ≤-refl (compAllRefl (UNIV 0) w) (compAllRefl (UNIV 0) w)

lemma2 : (w : 𝕎·) → eqtypes w (#UNIV 0) (#UNIV 0)
lemma2 w = impliesEqTypes 1 (lemma1 w)

lemma3 : (w : 𝕎·) → equalTypes 2 w (#UNIV 1) (#UNIV 1)
lemma3 w = EQTUNIV 1 ≤-refl (compAllRefl (UNIV 1) w) (compAllRefl (UNIV 1) w)

lemma4 : (w : 𝕎·) → eqtypes w (#UNIV 1) (#UNIV 1)
lemma4 w = impliesEqTypes 2 (lemma3 w)

lemma5 : (w : 𝕎·) → equalInType 2 w (#UNIV 1) (#UNIV 0) (#UNIV 0)
lemma5 w = (lemma3 w , Mod.∀𝕎-□ M (λ w' e → lemma1 w'))

lemma6 : (w : 𝕎·) → eqintype w (#UNIV 1) (#UNIV 0) (#UNIV 0)
lemma6 w = impliesEqInType 2 (lemma5 w)

lemma7 : (w : 𝕎·) → equalTypes 2 w (#UNIV 0) (#UNIV 0)
lemma7 w = EQTUNIV 0 0<1+n (compAllRefl (UNIV 0) w) (compAllRefl (UNIV 0) w)


wPredExtIrr-× : {w : 𝕎·} {f g : wPred w} → wPredExtIrr f → wPredExtIrr g → wPredExtIrr (λ w' e' → f w' e' × g w' e')
wPredExtIrr-× {w} {f} {g} wF wG w' e1 e2 (hf , hg) = wF w' e1 e2 hf , wG w' e1 e2 hg


wPredExtIrr-⇛ : {w : 𝕎·} {a b : Term} → wPredExtIrr {w} (λ w' e' → a ⇛ b at w')
wPredExtIrr-⇛ {w} {a} {b} w' e1 e2 h = h


-- Do we still need is-universe now?
is-universe : (u : univs) → Set(lsuc(L))
is-universe u = Lift {0ℓ} (lsuc(L)) ⊤
{--  (w : 𝕎·) (T1 T2 : CTerm)
  → fst (snd u) w T1 T2
  → □· w (λ w' _ → ⌜ T1 ⌝ ⇛ (UNIV (fst u)) at w' × ⌜ T2 ⌝ ⇛ (UNIV (fst u)) at w')
--}


{--
eqTypes-pres-eqInType-NAT : (u : univs) (isu : is-universe u) (w : 𝕎·) (A B a b : Term)
                            → A ⇛ NAT at w
                            → B ⇛ NAT at w
                            → □· w (λ w' _ → strongMonEq w' a b)
                            → (eqt2 : eqTypes u w A B) → eqInType u w eqt2 a b
--{-# INLINE ∀𝕎-inOpenBar-inOpenBar' #-}
{-# TERMINATING #-} -- inlining [Bar.∀𝕎-□-□' barI] works: uncomment c
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTNAT x x₁) = e
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTQNAT x x₁) = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTFREE x x₁) = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSQUASH A1 A2 x x₁ eqtA) = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTUNIV x) =
  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : □· w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTBAR x) = c
  where
    c2 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    c2 w2 e2 e' at = eqTypes-pres-eqInType-NAT u isu w2 A B a b (⇛-mon e2 c₁) (⇛-mon e2 c₂) (inOpenBar-mon e2 e) e'

    loc-∀𝕎-inOpenBar-inOpenBar' : (i : inOpenBar w (λ w' _ → eqTypes u w' A B)) → inOpenBar' w i (λ w' _ x → eqInType u w' x a b)
    loc-∀𝕎-inOpenBar-inOpenBar' i w1 e1 =
      w2 ,
      ⊑-refl· w2 ,
      λ w3 e3 z → c2 w3 z (h0 w3 (⊑-trans· (⊑-refl· w2) e3) z) {!ATOPENBAR w1 e1 w3 (⊑-trans· (⊑-refl· (proj₁ (i w1 e1))) e3) z!}
      where
        w2 : 𝕎·
        w2 = fst (i w1 e1)

        e2 : w2 ≽ w1
        e2 = fst (snd (i w1 e1))

        h0 : ∀𝕎 w2 (λ w3 e3 → (z : w3 ≽ w) → eqTypes u w3 A B)
        h0 = snd (snd (i w1 e1))

    c : □·' w x (λ w' _ (x : eqTypes u w' A B) → eqInType u w' x a b)
    -- Agda's termination checker fails on this, but accepts the one above, even though, they are exactly the same up to unfolding
    c = Bar.∀𝕎-□-□' barI x c2
    --c = loc-∀𝕎-inOpenBar-inOpenBar' x
--}




{--
eqTypes-pres-eqInType : (u : univs) (w : 𝕎·) (A B a b : Term) (eqt1 : eqTypes u w A B)
                        → eqInType u w eqt1 a b
                        → (eqt2 : eqTypes u w A B) → eqInType u w eqt2 a b
eqTypes-pres-eqInType u w A B a b (EQTNAT x x₁) e eqt2 = eqTypes-pres-eqInType-NAT u w A B a b x x₁ e eqt2
eqTypes-pres-eqInType u w A B a b (EQTQNAT x x₁) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTFREE x x₁) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTUNIV x) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTBAR x) e = {!!}--}


{--wPredExtIrr-eqInType : {w : 𝕎·} {u : univs} {A B a b : Term} (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A B))
                       → wPredExtIrr (λ w' e → eqInType u w' (eqtA w' e) a b)
wPredExtIrr-eqInType {w} {u} {A} {B} {a} {b} eqtA w' e1 e2 h = {!!}--}


wPredExtIrr-equalInType : {w : 𝕎·} {u : ℕ} {A a b : CTerm}
                          → wPredExtIrr {w} (λ w' e → equalInType u w' A a b)
wPredExtIrr-equalInType {w} {u} {A} {a} {b} w' e1 e2 h = h


wPredExtIrr-const : {w : 𝕎·} {F : 𝕎· → Set(lsuc(L))}
                    → wPredExtIrr {w} (λ w' e → F w')
wPredExtIrr-const {w} {F} w' e1 e2 h = h


-- Monotonicity
mon : (p : wper) → Set(lsuc(L))
mon p = {a b : CTerm} {w : 𝕎·} → p w a b → ∀𝕎 w (λ w' e' → p w' a b)


#strongMonEq-mon : mon #strongMonEq
#strongMonEq-mon {a} {b} {w} (n , c₁ , c₂) w1 e1 = (n , ⇛-mon e1 c₁ , ⇛-mon e1 c₂)


#weakMonEq-mon : mon #weakMonEq
#weakMonEq-mon {a} {b} {w} h w' e' = ∀𝕎-mon e' h


eqTypes-mon : (u : univs) → mon (eqTypes u)
eqTypes-mon u {A} {B} {w1} (EQTNAT x x₁) w2 ext = EQTNAT (⇛-mon ext x) (⇛-mon ext x₁)
eqTypes-mon u {A} {B} {w1} (EQTQNAT x x₁) w2 ext = EQTQNAT (⇛-mon ext x) (⇛-mon ext x₁)
eqTypes-mon u {A} {B} {w1} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) w2 ext =
  EQTLT a1 a2 b1 b2
    (⇛-mon ext x) (⇛-mon ext x₁)
    (#strongMonEq-mon {a1} {a2} x₂ w2 ext)
    (#strongMonEq-mon {b1} {b2} x₃ w2 ext)
eqTypes-mon u {A} {B} {w1} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) w2 ext =
  EQTQLT a1 a2 b1 b2
    (⇛-mon ext x) (⇛-mon ext x₁)
    (#weakMonEq-mon {a1} {a2} x₂ w2 ext)
    (#weakMonEq-mon {b1} {b2} x₃ w2 ext)
eqTypes-mon u {A} {B} {w1} (EQTFREE x x₁) w2 ext =
  EQTFREE (⇛-mon ext x) (⇛-mon ext x₁)
eqTypes-mon u {A} {B} {w1} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) w2 ext =
  EQTPI A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqta) (∀𝕎-mon ext eqtb) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqta w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b a₀ b₀ : CTerm) → wPredDepExtIrr (λ w e x₂ → eqInType u w (∀𝕎-mon ext eqtb w e a b x₂) a₀ b₀)
    extb' a b a₀ b₀ w' e1 e2 x1 x2 ei = extb a b a₀ b₀ w' (⊑-trans· ext e1) (⊑-trans· ext e2) x1 x2 ei

eqTypes-mon u {A} {B} {w1} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) w2 ext =
  EQTSUM A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqta) (∀𝕎-mon ext eqtb) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqta w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b a₀ b₀ : CTerm) → wPredDepExtIrr (λ w e x₂ → eqInType u w (∀𝕎-mon ext eqtb w e a b x₂) a₀ b₀)
    extb' a b a₀ b₀ w' e1 e2 x1 x2 ei = extb a b a₀ b₀ w' (⊑-trans· ext e1) (⊑-trans· ext e2) x1 x2 ei

eqTypes-mon u {A} {B} {w1} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) w2 ext =
  EQTSET A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqta) (∀𝕎-mon ext eqtb) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqta w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b a₀ b₀ : CTerm) → wPredDepExtIrr (λ w e x₂ → eqInType u w (∀𝕎-mon ext eqtb w e a b x₂) a₀ b₀)
    extb' a b a₀ b₀ w' e1 e2 x1 x2 ei = extb a b a₀ b₀ w' (⊑-trans· ext e1) (⊑-trans· ext e2) x1 x2 ei

eqTypes-mon u {A} {B} {w1} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) w2 ext =
  EQTEQ a1 b1 a2 b2 A₁ B₁ (⇛-mon ext x) (⇛-mon ext x₁)
    (∀𝕎-mon ext eqtA) exta' (∀𝕎-mon ext eqt1) (∀𝕎-mon ext eqt2)
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) w2 ext =
  EQTUNION A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) (∀𝕎-mon ext eqtB) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtB w e) a b)
    extb' a b w' e1 e2 ei = extb a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTSQUASH A1 A2 x x₁ eqtA exta) w2 ext =
  EQTSQUASH A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

{--eqTypes-mon u {A} {B} {w1} (EQTDUM A1 A2 x x₁ eqtA exta) w2 ext =
  EQTDUM A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei--}

eqTypes-mon u {A} {B} {w1} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) w2 ext =
  EQFFDEFS A1 A2 x1 x2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta' (∀𝕎-mon ext eqx)
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTUNIV i p c₁ c₂) w2 ext = EQTUNIV i p (⇛-mon ext c₁) (⇛-mon ext c₂) --(m x w2 ext)

eqTypes-mon u {A} {B} {w1} (EQTLIFT A1 A2 c₁ c₂ eqtA exta) w2 ext =
  EQTLIFT A1 A2 (⇛-mon ext c₁) (⇛-mon ext c₂) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTBAR x) w2 ext = EQTBAR (Mod.↑□ M x ext)




{--
  NOTE:
  This is the same as if-equalInType-EQ below, but where we've unfolded all abstractions to convince Agda
  that the function terminates (and splitting (eqt,eqi) into 2 separate arguments.
 --}
{--
if-equalInType-EQ-test : (u : ℕ) (w : 𝕎·) (T a b t₁ t₂ : CTerm)
                         (eqt : isType u w (#EQ a b T))
                         (eqi : equalTerms u w eqt t₁ t₂)
                         → □· w (λ w' e' → equalInType u w' T a b)
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTNAT x x₁) eqi = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTQNAT x x₁) eqi = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (EQneqLT (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTFREE x x₁) eqi = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (EQneqPI (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (EQneqSET (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) eqi
  rewrite #EQinj1 {a} {b} {T} {a1} {a2} {A} (#compAllVal x tt)  | #EQinj2 {a} {b} {T} {a1} {a2} {A} (#compAllVal x tt)  | #EQinj3 {a} {b} {T} {a1} {a2} {A} (#compAllVal x tt)
        | #EQinj1 {a1} {a2} {A} {b1} {b2} {B} (#compAllVal x₁ tt) | #EQinj2 {a1} {a2} {A} {b1} {b2} {B} (#compAllVal x₁ tt) | #EQinj3 {a1} {a2} {A} {b1} {b2} {B} (#compAllVal x₁ tt) =
  Bar.∀𝕎-□Func
    barI
    (λ w1 e1 eqi1 → eqtA w1 e1 , eqi1)
    eqi
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
--if-equalInType-EQ-test u w T a b t₁ t₂ (EQTDUM A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqDUM (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTUNIV i p c₁ c₂) eqi = ⊥-elim (EQneqUNIV (compAllVal c₁ tt)) --Bar.∀𝕎-□Func barI z2 x
{--  where
    z2 : ∀𝕎 w (λ w' e' → (#EQ a b T #⇛ #UNIV u at w' × #EQ a b T #⇛ #UNIV u at w') → t₁ #⇛ #AX at w' × t₂ #⇛ #AX at w' × equalInType u w' T a b)
    z2 w' e' (c₁ , c₂) = ⊥-elim (EQneqUNIV (compAllVal c₁ tt))--}
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTLIFT A1 A2 c1 c2 eqtA exta) eqi = ⊥-elim (EQneqLIFT (compAllVal c2 tt))
--if-equalInType-EQ-test u w T a b t₁ t₂ (EQTBAR x , eqi) =
if-equalInType-EQ-test u w T a b t₁ t₂ (EQTBAR x) eqi =
  inOpenBar-idem
    (λ w1 e1 →
      fst (eqi w1 e1 (fst (x w1 e1)) (⊑-refl· _)) ,
      ⊑-trans· (fst (snd (x w1 e1))) (fst (snd (eqi w1 e1 (fst (x w1 e1)) (⊑-refl· _)))) ,
      λ w4 e4 z → aw w4 z (snd (snd (x w1 e1)) w4 (⊑-trans· (⊑-refl· _) (⊑-trans· (fst (snd (eqi w1 e1 (fst (x w1 e1)) (⊑-refl· _)))) e4)) z) (snd (snd (eqi w1 e1 (fst (x w1 e1)) (⊑-refl· _))) w4 e4 (⊑-trans· (⊑-refl· _) (⊑-trans· (fst (snd (eqi w1 e1 (fst (x w1 e1)) (⊑-refl· _)))) e4)) z))
  where
    aw : ∀𝕎 w
              (λ w' e' →
                (x₁ : eqTypes (uni u) w' (#EQ a b T) (#EQ a b T))
                → eqInType (uni u) w' x₁ t₁ t₂
                → □· w' (↑wPred' (λ w'' e → equalInType u w'' T a b) e'))
    aw w1 e1 eqt1 eqi1 =
      λ w1 e1 →
        fst (h w1 e1) ,
        ⊑-trans· (fst (snd (h w1 e1))) (⊑-refl· (fst (h w1 e1))) ,
        λ w4 e4 z z₀ → snd (snd (h w1 e1)) w4 (⊑-trans· (⊑-refl· (fst (h w1 e1))) e4) z
      where
        h : inOpenBar w1 (λ w' e' → equalInType u w' T a b)
        h = if-equalInType-EQ-test u w1 T a b t₁ t₂ eqt1 eqi1
--}



{--
  NOTE:
  if-equalInType-EQ-test above shows that we don't need 'TERMINATING' when we unfold all abstractions.
  If we don't Agda can't figure out it's terminating.
  Also, we need to split the pair (eqt,eqi) into 2 arguments, otherwise again Agda can't figure out that it's terminating.
 --}
if-equalInType-EQ : (u : ℕ) (w : 𝕎·) (T a b t₁ t₂ : CTerm)
                    → equalInType u w (#EQ a b T) t₁ t₂
                    → □· w (λ w' e' → equalInType u w' T a b)
{-# INLINE □· #-}
{-# TERMINATING #-}
if-equalInType-EQ u w T a b t₁ t₂ (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqPI (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSET (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2 , eqi)
  rewrite #EQinj1 {a} {b} {T} {a1} {a2} {A} (#compAllVal x tt)  | #EQinj2 {a} {b} {T} {a1} {a2} {A} (#compAllVal x tt)  | #EQinj3 {a} {b} {T} {a1} {a2} {A} (#compAllVal x tt)
        | #EQinj1 {a1} {a2} {A} {b1} {b2} {B} (#compAllVal x₁ tt) | #EQinj2 {a1} {a2} {A} {b1} {b2} {B} (#compAllVal x₁ tt) | #EQinj3 {a1} {a2} {A} {b1} {b2} {B} (#compAllVal x₁ tt) =
  Mod.∀𝕎-□Func M
    (λ w1 e1 eqi1 → eqtA w1 e1 , eqi1)
    eqi
if-equalInType-EQ u w T a b t₁ t₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
--if-equalInType-EQ u w T a b t₁ t₂ (EQTDUM A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqDUM (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTUNIV i p c₁ c₂ , eqi) = ⊥-elim (EQneqUNIV (compAllVal c₁ tt)) --Bar.∀𝕎-□Func barI z2 x
{--  where
    z2 : ∀𝕎 w (λ w' e' → (#EQ a b T #⇛ #UNIV u at w' × #EQ a b T #⇛ #UNIV u at w') → t₁ #⇛ #AX at w' × t₂ #⇛ #AX at w' × equalInType u w' T a b)
    z2 w' e' (c₁ , c₂) = ⊥-elim (EQneqUNIV (compAllVal c₁ tt))--}
if-equalInType-EQ u w T a b t₁ t₂ (EQTLIFT A1 A2 c1 c2 eqtA exta , eqi) = ⊥-elim (EQneqLIFT (compAllVal c2 tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w
              (λ w' e' →
                (x₁ : eqTypes (uni u) w' (#EQ a b T) (#EQ a b T))
                {--(at : atbar x w' e' x₁)--}
                → eqInType (uni u) w' x₁ t₁ t₂
                → □· w' (↑wPred' (λ w'' e → equalInType u w'' T a b) e'))
    aw w1 e1 eqt1 {--at--} eqi1 = Mod.∀𝕎-□Func M (λ w' e' x z → x) ind
      where
        ind : □· w1 (λ w' e' → equalInType u w' T a b)
        ind = if-equalInType-EQ u w1 T a b t₁ t₂ (eqt1 , eqi1)



{--
TODO: keep unfolding by hand
  IS𝔹-fam {w} (IS𝔹-fam2 {w} (fst x) (λ {w'} e ib b' → inIS𝔹Dep b' (snd x e ib) (↑wPredDep'' {!!} e)) eqi)
               (λ w1 e1 z b' → inIS𝔹 b' (↑wPred' {!!} z)) i' ,
  {!!}
  where
--    g : wPredDep
    aw : ∀𝕎 w
              (λ w' e' →
                (x₁ : eqTypes (uni u) w' (#EQ a b T) (#EQ a b T))
                {--(at : atbar x w' e' x₁)--}
                → eqInType (uni u) w' x₁ t₁ t₂
                → □· w' (↑wPred' (λ w'' e → ⌜ t₁ ⌝ ⇛ AX at w'' × ⌜ t₂ ⌝ ⇛ AX at w'' × equalInType u w'' T a b) e'))
    aw w1 e1 eqt1 {--at--} eqi1 = ∀𝕎-inBethBarFunc (λ w' e' x z → x) ind
      where
        ind : □· w1 (λ w' e' → ⌜ t₁ ⌝ ⇛ AX at w' × ⌜ t₂ ⌝ ⇛ AX at w' × equalInType u w' T a b)
        ind = if-equalInType-EQ u w1 T a b t₁ t₂ (eqt1 , eqi1)

    i' : inIS𝔹 (IS𝔹-fam2 {w} (fst x) (λ {w'} e ib b' → inIS𝔹Dep b' (snd x e ib) (↑wPredDep'' {!!} e)) eqi) {!!}
    i' {w'} e (mkIS𝔹In w2 e2 br , F) w1 e1 z =
      aw w1 z
         (snd x e2 br w1 (⊑-trans· (IS𝔹.ext (fst (eqi e2 br)) F) e1) z)
         (snd (eqi e2 br)
              (IS𝔹.ext (fst (eqi e2 br)) F)
              F w1 e1
              (⊑-trans· (IS𝔹.ext (fst (eqi e2 br)) F) e1)
              z)
--}



□·-strongMonEq-sym : {w : 𝕎·} {a b : Term}
                        → □· w (λ w' _ → strongMonEq w' a b)
                        → □· w (λ w' _ → strongMonEq w' b a)
□·-strongMonEq-sym {w} {a} {b} h =
  Mod.∀𝕎-□Func M (λ w1 e1 → strongMonEq-sym) h




□·-strongMonEq-trans : {w : 𝕎·} {a b c : Term}
                          → □· w (λ w' _ → strongMonEq w' a b)
                          → □· w (λ w' _ → strongMonEq w' b c)
                          → □· w (λ w' _ → strongMonEq w' a c)
□·-strongMonEq-trans {w} {a} {b} {c} h₁ h₂ =
  Mod.□Func M (Mod.∀𝕎-□Func M aw h₁) h₂
  where
    aw : ∀𝕎 w (λ w' e' → strongMonEq w' a b → strongMonEq w' b c → strongMonEq w' a c)
    aw w1 e1 = strongMonEq-trans



□·-weakMonEq-sym : {w : 𝕎·} {a b : Term}
                        → □· w (λ w' _ → weakMonEq w' a b)
                        → □· w (λ w' _ → weakMonEq w' b a)
□·-weakMonEq-sym {w} {a} {b} h =
  Mod.∀𝕎-□Func M (λ w1 e1 → weakMonEq-sym) h




□·-weakMonEq-trans : {w : 𝕎·} {a b c : Term}
                        → □· w (λ w' _ → weakMonEq w' a b)
                        → □· w (λ w' _ → weakMonEq w' b c)
                        → □· w (λ w' _ → weakMonEq w' a c)
□·-weakMonEq-trans {w} {a} {b} {c} h₁ h₂ =
  Mod.□Func M (Mod.∀𝕎-□Func M aw h₁) h₂
  where
    aw : ∀𝕎 w (λ w' e' → weakMonEq w' a b → weakMonEq w' b c → weakMonEq w' a c)
    aw w1 e1 = weakMonEq-trans


strongMonEq-pres-⇓ : {w : 𝕎·} {a1 a2 : Term} {n : ℕ}
                     → strongMonEq w a1 a2
                     → a1 ⇓ NUM n at w
                     → a2 ⇓ NUM n at w
strongMonEq-pres-⇓ {w} {a1} {a2} {n} (m , c₁ , c₂) c = z₂
  where
    z₁ : NUM n ≡ NUM m
    z₁ = ⇓-val-det tt tt c (lower (c₁ w (⊑-refl· _)))

    z₂ : a2 ⇓ NUM n at w
    z₂ rewrite NUMinj z₁ = lower (c₂ w (⊑-refl· _))



weakMonEq-pres-⇓ : {w : 𝕎·} {a1 a2 : Term} {n : ℕ}
                   → weakMonEq w a1 a2
                   → a1 ⇓ NUM n at w
                   → a2 ⇓ NUM n at w
weakMonEq-pres-⇓ {w} {a1} {a2} {n} wm c = z₂
  where
    m : ℕ
    m = fst (lower (wm w (⊑-refl· _)))

    z₁ : NUM n ≡ NUM m
    z₁ = ⇓-val-det tt tt c (fst (snd (lower (wm w (⊑-refl· _)))))

    z₂ : a2 ⇓ NUM n at w
    z₂ rewrite NUMinj z₁ = snd (snd (lower (wm w (⊑-refl· _))))


weakMonEq-preserves-□· : {w : 𝕎·} {a b c d : CTerm}
                            → weakMonEq w ⌜ c ⌝ ⌜ a ⌝
                            → weakMonEq w ⌜ d ⌝ ⌜ b ⌝
                            → □· w (λ w' _ → lift-<NUM-pair w' ⌜ a ⌝ ⌜ b ⌝)
                            → □· w (λ w' _ → lift-<NUM-pair w' ⌜ c ⌝ ⌜ d ⌝)
weakMonEq-preserves-□· {w} {a} {b} {c} {d} s₁ s₂ i =
  Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w (λ w' e' → lift-<NUM-pair w' ⌜ a ⌝ ⌜ b ⌝ → lift-<NUM-pair w' ⌜ c ⌝ ⌜ d ⌝)
    aw w1 e1 (lift (n , m , c₁ , c₂ , c')) =
      lift (n , m ,
            weakMonEq-pres-⇓ (weakMonEq-sym (#weakMonEq-mon {c} {a} s₁ w1 e1)) c₁ ,
            weakMonEq-pres-⇓ (weakMonEq-sym (#weakMonEq-mon {d} {b} s₂ w1 e1)) c₂ ,
            c')



strongMonEq-preserves-□· : {w : 𝕎·} {a b c d : CTerm}
                              → strongMonEq w ⌜ c ⌝ ⌜ a ⌝
                              → strongMonEq w ⌜ d ⌝ ⌜ b ⌝
                              → □· w (λ w' _ → lift-<NUM-pair w' ⌜ a ⌝ ⌜ b ⌝)
                              → □· w (λ w' _ → lift-<NUM-pair w' ⌜ c ⌝ ⌜ d ⌝)
strongMonEq-preserves-□· {w} {a} {b} {c} {d} s₁ s₂ i =
  Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w (λ w' e' → lift-<NUM-pair w' ⌜ a ⌝ ⌜ b ⌝ → lift-<NUM-pair w' ⌜ c ⌝ ⌜ d ⌝)
    aw w1 e1 (lift (n , m , c₁ , c₂ , c')) =
      lift (n , m ,
            strongMonEq-pres-⇓ (strongMonEq-sym (#strongMonEq-mon {c} {a} s₁ w1 e1)) c₁ ,
            strongMonEq-pres-⇓ (strongMonEq-sym (#strongMonEq-mon {d} {b} s₂ w1 e1)) c₂ ,
            c')


→□·⇛ : {w : 𝕎·} {A B : Term}
            → A ⇛ B at w
            → □· w (λ w' _ → A ⇛ B at w')
→□·⇛ {w} {A} {B} comp = Mod.∀𝕎-□ M (λ w1 e1 → ⇛-mon e1 comp)



⇛to-same-CS-sym : {w : 𝕎·} {a b : Term}
                  → ⇛to-same-CS w a b
                  → ⇛to-same-CS w b a
⇛to-same-CS-sym {w} {a} {b} (n , c₁ , c₂) = n , c₂ , c₁



□·-⇛to-same-CS-sym : {w : 𝕎·} {a b : Term}
                        → □· w (λ w' _ → ⇛to-same-CS w' a b)
                        → □· w (λ w' _ → ⇛to-same-CS w' b a)
□·-⇛to-same-CS-sym {w} {a} {b} h =
  Mod.∀𝕎-□Func M (λ w1 e1 → ⇛to-same-CS-sym) h


CSinj : {n m : Name} → CS n ≡ CS m → n ≡ m
CSinj refl =  refl


⇛to-same-CS-trans : {w : 𝕎·} {a b c : Term}
                    → ⇛to-same-CS w a b
                    → ⇛to-same-CS w b c
                    → ⇛to-same-CS w a c
⇛to-same-CS-trans {w} {a} {b} {c} (n , c₁ , c₂) (m , d₁ , d₂) rewrite CSinj (⇛-val-det tt tt d₁ c₂) = n , c₁ , d₂

□·-⇛to-same-CS-trans : {w : 𝕎·} {a b c : Term}
                          → □· w (λ w' _ → ⇛to-same-CS w' a b)
                          → □· w (λ w' _ → ⇛to-same-CS w' b c)
                          → □· w (λ w' _ → ⇛to-same-CS w' a c)
□·-⇛to-same-CS-trans {w} {a} {b} {c} h₁ h₂ =
  Mod.□Func M (Mod.∀𝕎-□Func M aw h₁) h₂
  where
    aw : ∀𝕎 w (λ w' e' → ⇛to-same-CS w' a b → ⇛to-same-CS w' b c → ⇛to-same-CS w' a c)
    aw w1 e1 = ⇛to-same-CS-trans



{--
-- we can't characerize eqt like that as it might be a tower of EQTBAR
eqTypes⇛NAT : {u : univs} {w : 𝕎·} {A B : CTerm}
               → (eqt : eqTypes u w A B)
               → A #⇛ #NAT at w
               → □· w (λ w' _ → ⌜ B ⌝ ⇛ NAT at w')
eqTypes⇛NAT {u} {w} {A} {B} (EQTNAT x x₁) comp = →□·⇛ x₁
eqTypes⇛NAT {u} {w} {A} {B} (EQTQNAT x x₁) comp = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) comp = ⊥-elim (NATneqLT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) comp = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTFREE x x₁) comp = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqPI (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqSET (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) comp = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) comp = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA exta) comp = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp x))
--eqTypes⇛NAT {u} {w} {A} {B} (EQTDUM A1 A2 x x₁ eqtA exta) comp = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) comp = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTUNIV i p c₁ c₂) comp = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ #UNIV (fst u) at w' × B #⇛ #UNIV (fst u) at w')
    z = {!!} --isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 comp) d₁)))--}
eqTypes⇛NAT {u} {w} {A} {B} (EQTLIFT A1 A2 c1 c2 eqtA exta) comp = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp c1))
eqTypes⇛NAT {u} {w} {A} {B} (EQTBAR x) comp = i
  where
    a : ∀𝕎 w (λ w' e' → eqTypes u w' A B → □· w' (λ w'' _ → ⌜ B ⌝ ⇛ NAT at w''))
    a w1 e1 eqt = eqTypes⇛NAT eqt (⇛-mon e1 comp)

    q : wPred w
    q = λ w' _ → eqTypes u w' A B

    g : wPred w
    g = λ w' _ → □· w' (λ w'' _ → ⌜ B ⌝ ⇛ NAT at w'')

    loc-∀𝕎-inOpenBarFunc : inOpenBar w q → inOpenBar w g
    loc-∀𝕎-inOpenBarFunc h w1 e1 =
      w2 , e2 , h3
      where
        h1 : ∃∀𝕎 w1 λ w2 e2 → (z : w ⊑· w2) → q w2 z
        h1 = h w1 e1

        w2 : 𝕎·
        w2 = fst h1

        e2 : w1 ⊑· w2
        e2 = fst (snd h1)

        h2 : ∀𝕎 w2 λ w3 e3 → (z : w ⊑· w3) → q w3 z
        h2 = snd (snd h1)

        h3 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → g w3 z)
        h3 w3 e3 z = a w3 z (h2 w3 e3 z)

    j : □· w (λ w' _ → □· w' (λ w'' _ → ⌜ B ⌝ ⇛ NAT at w''))
    j = loc-∀𝕎-inOpenBarFunc x
    --j = Mod.∀𝕎-□Func M a x

    f : wPred w
    f = λ w' _ → ⌜ B ⌝ ⇛ NAT at w'

    loc-inOpenBar-idem : wPredExtIrr f
                         → inOpenBar w f
    loc-inOpenBar-idem ei w1 e1 =
      fst h4 ,
      ⊑-trans· e2 (fst (snd h4)) ,
      λ w3 e3 z → ei w3 (⊑-trans· (⊑-trans· e1 e2) (⊑-trans· (fst (snd h4)) e3)) z (snd (snd h4) w3 e3 (⊑-trans· (fst (snd h4)) e3))
      where
        w2 : 𝕎·
        w2 = fst (j w1 e1)

        e2 : w1 ⊑· w2
        e2 = fst (snd (j w1 e1))

        h2 : ∀𝕎 w2 (λ w' e' → (z : w ⊑· w') → inOpenBar w' (↑wPred f z))
        h2 = snd (snd (j w1 e1))

        h3 : inOpenBar w2 (↑wPred f (⊑-trans· e1 e2))
        h3 = h2 w2 (⊑-refl· w2) (⊑-trans· e1 e2)

        h4 : ∃∀𝕎 w2 (λ w' e' → (z : w2 ⊑· w') → f w' (⊑-trans· (⊑-trans· e1 e2) z))
        h4 = h3 w2 (⊑-refl· w2)

    i : □· w (λ w' _ → ⌜ B ⌝ ⇛ NAT at w')
    --i = Mod.□-idem M wPredExtIrr-⇛ j
    i = loc-inOpenBar-idem wPredExtIrr-⇛
--}


eqTypesTrans : (u : univs) (w : 𝕎·) (A B : CTerm) → Set(lsuc(L))
eqTypesTrans u w A B = (C : CTerm) → eqTypes u w B C → eqTypes u w A C

eqInTypeSym : (u : univs) {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeSym u {w} {A} {B} eqt = (a b : CTerm) → eqInType u w eqt a b → eqInType u w eqt b a

eqInTypeTrans : (u : univs) {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeTrans u {w} {A} {B} eqt = (a b c : CTerm) → eqInType u w eqt a b → eqInType u w eqt b c → eqInType u w eqt a c

eqInTypeExt : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExt {u} {w} {A} {B} eqt =
  (eqt' : eqTypes u w A B) (a b : CTerm)
  → (eqInType u w eqt a b → eqInType u w eqt' a b) × (eqInType u w eqt' a b → eqInType u w eqt a b)

eqInTypeExtL1 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtL1 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w A C) (a b : CTerm) → eqInType u w eqt a b → eqInType u w eqt' a b

eqInTypeExtL2 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtL2 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w C A) (a b : CTerm) → eqInType u w eqt a b → eqInType u w eqt' a b

eqInTypeExtR1 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtR1 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w C B) (a b : CTerm) → eqInType u w eqt a b → eqInType u w eqt' a b

eqInTypeExtR2 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtR2 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w B C) (a b : CTerm) → eqInType u w eqt a b → eqInType u w eqt' a b

eqInTypeExtRevL1 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtRevL1 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w A C) (a b : CTerm) → eqInType u w eqt' a b → eqInType u w eqt a b

eqInTypeExtRevL2 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtRevL2 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w C A) (a b : CTerm) → eqInType u w eqt' a b → eqInType u w eqt a b

eqInTypeExtRevR1 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtRevR1 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w C B) (a b : CTerm) → eqInType u w eqt' a b → eqInType u w eqt a b

eqInTypeExtRevR2 : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeExtRevR2 {u} {w} {A} {B} eqt = (C : CTerm) (eqt' : eqTypes u w B C) (a b : CTerm) → eqInType u w eqt' a b → eqInType u w eqt a b

eqInTypeLocal : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → Set(lsuc(L))
eqInTypeLocal {u} {w} {A} {B} eqt =
  (a b : CTerm)
  → (i : □· w (λ w' e → eqTypes u w' A B))
  → □·' w i (λ w' e z → eqInType u w' z a b)
  → eqInType u w eqt a b


-- Type System Props
record TSP {u : univs} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) : Set(lsuc(L)) where
  constructor mktsp
  field
    tsym     : eqTypes u w B A
    ttrans   : eqTypesTrans u w A B
    isym     : eqInTypeSym u eqt
    itrans   : eqInTypeTrans u eqt
    extl1    : eqInTypeExtL1 eqt
    extl2    : eqInTypeExtL2 eqt
    extr1    : eqInTypeExtR1 eqt
    extr2    : eqInTypeExtR2 eqt
    extrevl1 : eqInTypeExtRevL1 eqt
    extrevl2 : eqInTypeExtRevL2 eqt
    extrevr1 : eqInTypeExtRevR1 eqt
    extrevr2 : eqInTypeExtRevR2 eqt
    local    : eqInTypeLocal eqt


TSP-refl : {u : univs} {w : 𝕎·} {A1 A2 a1 a2 : CTerm}
           {w1 : 𝕎·} {e1 : w ⊑· w1}
           {eqta : ∀𝕎 w (λ w1 e1 → eqTypes u w1 A1 A2)}
           → ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1))
           → eqInType u w1 (eqta w1 e1) a1 a2
           → eqInType u w1 (eqta w1 e1) a1 a1
TSP-refl {u} {w} {A1} {A2} {a1} {a2} {w1} {e1} {eqta} aw i =
  TSP.itrans (aw w1 e1) a1 a2 a1 i (TSP.isym (aw w1 e1) a1 a2 i)



TSP-fam-rev-dom : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0} {a1 a2 f g : CTerm}
                  (eqta  : ∀𝕎 w (λ w1 e1 → eqTypes u w1 A1 A2))
                  (eqtb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) → eqInType u w1 (eqta w1 e1) a1 a2 → eqTypes u w1 (sub0 a1 B1) (sub0 a2 B2)))
                  (inda  : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → TSP (eqtb w1 e1 a1 a2 ea)))
                  {w1 : 𝕎·} {e1 : w ⊑· w1}
                  {ea1 : eqInType u w1 (eqta w1 e1) a1 a2}
                  {ea2 : eqInType u w1 (eqta w1 e1) a2 a1}
                  → eqInType u w1 (eqtb w1 e1 a1 a2 ea1) f g
                  → eqInType u w1 (eqtb w1 e1 a2 a1 ea2) f g
TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} {a1} {a2} {f} {g} eqta eqtb inda indb {w1} {e1} {ea1} {ea2} h =
  TSP.extl1 (indb w1 e1 a2 a2 ea22) (sub0 a1 B2) (eqtb w1 e1 a2 a1 ea2) f g ef1
  where
    ea22 : eqInType u w1 (eqta w1 e1) a2 a2
    ea22 = TSP.itrans (inda w1 e1) a2 a1 a2 ea2 ea1

    ef1 : eqInType u w1 (eqtb w1 e1 a2 a2 ea22) f g
    ef1 = TSP.extrevr1 (indb w1 e1 a2 a2 ea22) (sub0 a1 B1) (eqtb w1 e1 a1 a2 ea1) f g h



TSP-fam-rev-dom2 : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0} {a1 a2 a3 f g : CTerm}
                   (eqta  : ∀𝕎 w (λ w1 e1 → eqTypes u w1 A1 A2))
                   (eqtb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) → eqInType u w1 (eqta w1 e1) a1 a2 → eqTypes u w1 (sub0 a1 B1) (sub0 a2 B2)))
                   (inda  : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                   (indb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → TSP (eqtb w1 e1 a1 a2 ea)))
                   {w1 : 𝕎·} {e1 : w ⊑· w1}
                   {ea1 : eqInType u w1 (eqta w1 e1) a1 a2}
                   {ea2 : eqInType u w1 (eqta w1 e1) a2 a3}
                   → eqInType u w1 (eqtb w1 e1 a1 a2 ea1) f g
                   → eqInType u w1 (eqtb w1 e1 a2 a3 ea2) f g
TSP-fam-rev-dom2 {u} {w} {A1} {A2} {B1} {B2} {a1} {a2} {a3} {f} {g} eqta eqtb inda indb {w1} {e1} {ea1} {ea2} h =
  TSP.extl1 (indb w1 e1 a2 a2 ea22) (sub0 a3 B2) (eqtb w1 e1 a2 a3 ea2) f g ef1
  where
    ea22 : eqInType u w1 (eqta w1 e1) a2 a2
    ea22 = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 ea1) ea1

    ef1 : eqInType u w1 (eqtb w1 e1 a2 a2 ea22) f g
    ef1 = TSP.extrevr1 (indb w1 e1 a2 a2 ea22) (sub0 a1 B1) (eqtb w1 e1 a1 a2 ea1) f g h



TSP-fam-rev-dom3 : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0} {a1 a2 a3 f g : CTerm}
                   (eqta  : ∀𝕎 w (λ w1 e1 → eqTypes u w1 A1 A2))
                   (eqtb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) → eqInType u w1 (eqta w1 e1) a1 a2 → eqTypes u w1 (sub0 a1 B1) (sub0 a2 B2)))
                   (inda  : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                   (indb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → TSP (eqtb w1 e1 a1 a2 ea)))
                   {w1 : 𝕎·} {e1 : w ⊑· w1}
                   {ea1 : eqInType u w1 (eqta w1 e1) a1 a2}
                   {ea2 : eqInType u w1 (eqta w1 e1) a3 a1}
                   → eqInType u w1 (eqtb w1 e1 a1 a2 ea1) f g
                   → eqInType u w1 (eqtb w1 e1 a3 a1 ea2) f g
TSP-fam-rev-dom3 {u} {w} {A1} {A2} {B1} {B2} {a1} {a2} {a3} {f} {g} eqta eqtb inda indb {w1} {e1} {ea1} {ea2} h =
  TSP.extr1 (indb w1 e1 a1 a1 ea3) (sub0 a3 B1) (eqtb w1 e1 a3 a1 ea2) f g ef1
  where
    ea3 : eqInType u w1 (eqta w1 e1) a1 a1
    ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea1 (TSP.isym (inda w1 e1) a1 a2 ea1)

    ef1 : eqInType u w1 (eqtb w1 e1 a1 a1 ea3) f g
    ef1 = TSP.extrevl1 (indb w1 e1 a1 a1 ea3) (sub0 a2 B2) (eqtb w1 e1 a1 a2 ea1) f g h



TSP-fam-rev-dom4 : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0} {a1 a2 a3 f g : CTerm}
                   (eqta  : ∀𝕎 w (λ w1 e1 → eqTypes u w1 A1 A2))
                   (eqtb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) → eqInType u w1 (eqta w1 e1) a1 a2 → eqTypes u w1 (sub0 a1 B1) (sub0 a2 B2)))
                   (inda  : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                   (indb  : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → TSP (eqtb w1 e1 a1 a2 ea)))
                   {w1 : 𝕎·} {e1 : w ⊑· w1}
                   {ea1 : eqInType u w1 (eqta w1 e1) a1 a2}
                   {ea2 : eqInType u w1 (eqta w1 e1) a1 a3}
                   → eqInType u w1 (eqtb w1 e1 a1 a2 ea1) f g
                   → eqInType u w1 (eqtb w1 e1 a1 a3 ea2) f g
TSP-fam-rev-dom4 {u} {w} {A1} {A2} {B1} {B2} {a1} {a2} {a3} {f} {g} eqta eqtb inda indb {w1} {e1} {ea1} {ea2} h =
  TSP.extl1 (indb w1 e1 a1 a1 ea3) (sub0 a3 B2) (eqtb w1 e1 a1 a3 ea2) f g ef1
  where
    ea3 : eqInType u w1 (eqta w1 e1) a1 a1
    ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea1 (TSP.isym (inda w1 e1) a1 a2 ea1)

    ef1 : eqInType u w1 (eqtb w1 e1 a1 a1 ea3) f g
    ef1 = TSP.extrevl1 (indb w1 e1 a1 a1 ea3) (sub0 a2 B2) (eqtb w1 e1 a1 a2 ea1) f g h


irr-fam-pi : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
             (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
             (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
             → ∀𝕎 w1 (λ w' e' → PIeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) f g
                                 → (z : w ⊑· w') → PIeq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) f g)
irr-fam-pi u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' j z a1 a2 eqa =
  extb a1 a2 (#APPLY f a1) (#APPLY g a2) w' (⊑-trans· e1 e') z eqa' eqa (j a1 a2 eqa')
    where
      eqa' : eqInType u w' (eqta w' (⊑-trans· e1 e')) a1 a2
      eqa' = exta a1 a2 w' z (⊑-trans· e1 e') eqa


irr-fam-sum : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → SUMeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) w' f g
                                  → (z : w ⊑· w') → SUMeq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) w' f g)
irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' (a1 , a2 , b1 , b2 , eqa , c1 , c2 , eqb) z =
  a1 , a2 , b1 , b2 , eqa' , c1 , c2 , eqb'
    where
      eqa' : eqInType u w' (eqta w' z) a1 a2
      eqa' = exta a1 a2 w' (⊑-trans· e1 e') z eqa

      eqb' : eqInType u w' (eqtb w' z a1 a2 eqa') b1 b2
      eqb' = extb a1 a2 b1 b2 w' (⊑-trans· e1 e') z eqa eqa' eqb


irr-fam-set : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → SETeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) f g
                                  → (z : w ⊑· w') → SETeq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) f g)
irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' (b , eqa , eqb) z =
  b , eqa' , eqb'
    where
      eqa' : eqInType u w' (eqta w' z) f g
      eqa' = exta f g w' (⊑-trans· e1 e') z eqa

      eqb' : eqInType u w' (eqtb w' z f g eqa') b b
      eqb' = extb f g b b w' (⊑-trans· e1 e') z eqa eqa' eqb



irr-eq : (u : univs) (w : 𝕎·) (a1 a2 A1 A2 : CTerm)
         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
         (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
         → ∀𝕎 w1 (λ w' e' → EQeq a1 a2 (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' f g
                             → (z : w ⊑· w') → EQeq a1 a2 (eqInType u w' (eqta w' z)) w' f g)
irr-eq u w a1 a2 A1 A2 eqta exta f g w1 e1 w' e' eqa z = eqa'
  where
    eqa' : eqInType u w' (eqta w' z) a1 a2
    eqa' = exta a1 a2 w' (⊑-trans· e1 e') z eqa


irr-union : (u : univs) (w : 𝕎·) (A1 A2 B1 B2 : CTerm)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
            → ∀𝕎 w1 (λ w' e' → UNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) w' f g
                                → (z : w ⊑· w') → UNIONeq (eqInType u w' (eqta w' z)) (eqInType u w' (eqtb w' z)) w' f g)
irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1 w' e' (a , b , inj₁ (c₁ , c₂ , eqa)) z =
  a , b , inj₁ (c₁ , c₂ , eqa')
  where
    eqa' : eqInType u w' (eqta w' z) a b
    eqa' = exta a b w' (⊑-trans· e1 e') z eqa
irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1 w' e' (a , b , inj₂ (c₁ , c₂ , eqb)) z =
  a , b , inj₂ (c₁ , c₂ , eqb')
  where
    eqb' : eqInType u w' (eqtb w' z) a b
    eqb' = extb a b w' (⊑-trans· e1 e') z eqb



data TSQUASH-eq (eqa : per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
data TSQUASH-eq eqa w t1 t2 where
  TSQUASH-eq-base : (a1 a2 : CTerm) → #isValue a1 → #isValue a2 → ∼C w t1 a1 → ∼C w t2 a2 → eqa a1 a2 → TSQUASH-eq eqa w t1 t2
  TSQUASH-eq-trans : (t : CTerm) → TSQUASH-eq eqa w t1 t → TSQUASH-eq eqa w t t2 → TSQUASH-eq eqa w t1 t2


→TSQUASH-eq : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
               → TSQUASHeq eqa w t1 t2
               → TSQUASH-eq eqa w t1 t2
→TSQUASH-eq {eqa} {w} {t1} {t2} (0 , a1 , a2 , i1 , i2 , c1 , c2 , ea) = TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea
→TSQUASH-eq {eqa} {w} {t1} {t2} (suc n , t , (a1 , a2 , i1 , i2 , c1 , c2 , ea) , q) =
  TSQUASH-eq-trans t (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) (→TSQUASH-eq (n , q))




TSQUASHeqℕ-trans : {n m : ℕ} {eqa : per} {w : 𝕎·} {t1 t2 t3 : CTerm}
                 → TSQUASHeqℕ n eqa w t1 t2
                 → TSQUASHeqℕ m eqa w t2 t3
                 → TSQUASHeqℕ (n + suc m) eqa w t1 t3
TSQUASHeqℕ-trans {0} {m} {eqa} {w} {t1} {t2} {t3} h q = t2 , h , q
TSQUASHeqℕ-trans {suc n} {m} {eqa} {w} {t1} {t2} {t3} (t , h0 , h1) q = t , h0 , TSQUASHeqℕ-trans h1 q


TSQUASHeq-trans : {eqa : per} {w : 𝕎·} {t1 t2 t3 : CTerm}
                 → TSQUASHeq eqa w t1 t2
                 → TSQUASHeq eqa w t2 t3
                 → TSQUASHeq eqa w t1 t3
TSQUASHeq-trans {eqa} {w} {t1} {t2} {t3} (n , h) (m , q) = n + suc m , TSQUASHeqℕ-trans h q



TSQUASH-eq→ : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
               → TSQUASH-eq eqa w t1 t2
               → TSQUASHeq eqa w t1 t2
TSQUASH-eq→ {eqa} {w} {t1} {t2} (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 a) = 0 , a1 , a2 , i1 , i2 , c1 , c2 , a
TSQUASH-eq→ {eqa} {w} {t1} {t2} (TSQUASH-eq-trans t h1 h2) = TSQUASHeq-trans (TSQUASH-eq→ h1) (TSQUASH-eq→ h2)


TSQUASH-eq-sym : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → TSQUASH-eq eqa w t1 t2
                 → TSQUASH-eq eqa w t2 t1
TSQUASH-eq-sym {eqa} {w} {t1} {t2} sym (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) = TSQUASH-eq-base a2 a1 i2 i1 c2 c1 (sym a1 a2 ea)
TSQUASH-eq-sym {eqa} {w} {t1} {t2} sym (TSQUASH-eq-trans t h1 h2) =
  TSQUASH-eq-trans t (TSQUASH-eq-sym sym h2) (TSQUASH-eq-sym sym h1)



TSQUASHeq-sym : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → TSQUASHeq eqa w t1 t2
                 → TSQUASHeq eqa w t2 t1
TSQUASHeq-sym {eqa} {w} {t1} {t2} sym h = TSQUASH-eq→ (TSQUASH-eq-sym sym (→TSQUASH-eq h))



→TSQUASHeqℕ-suc : {n : ℕ} {eqa : per} {w : 𝕎·} {t1 t2 : CTerm} (t : CTerm)
                    → TSQUASHeqℕ n eqa w t1 t
                    → TSQUASHeqBase eqa w t t2
                    → TSQUASHeqℕ (suc n) eqa w t1 t2
→TSQUASHeqℕ-suc {0} {eqa} {w} {t1} {t2} t h q = t , h , q
→TSQUASHeqℕ-suc {suc n} {eqa} {w} {t1} {t2} t (t0 , h0 , h1) q = t0 , h0 , →TSQUASHeqℕ-suc {n} t h1 q



TSQUASH-eq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                 → TSQUASH-eq eqa1 w t1 t2
                 → TSQUASH-eq eqa2 w t1 t2
TSQUASH-eq-ext-eq {eqa} {w} {t1} {t2} ext (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  TSQUASH-eq-base a1 a2 i1 i2 c1 c2 (ext a1 a2 ea)
TSQUASH-eq-ext-eq {eqa} {w} {t1} {t2} ext (TSQUASH-eq-trans t h1 h2) =
  TSQUASH-eq-trans t (TSQUASH-eq-ext-eq ext h1) (TSQUASH-eq-ext-eq ext h2)



TSQUASHeq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                 → TSQUASHeq eqa1 w t1 t2
                 → TSQUASHeq eqa2 w t1 t2
TSQUASHeq-ext-eq {eqa} {w} {t1} {t2} ext h = TSQUASH-eq→ (TSQUASH-eq-ext-eq ext (→TSQUASH-eq h))



irr-TSQUASHeq : {u : univs} {w w' : 𝕎·} {A1 A2 : CTerm}
                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                {f g : CTerm}
                (e1 e2 : w ⊑· w')
                → TSQUASHeq (eqInType u w' (eqta w' e1)) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e2)) w' f g
irr-TSQUASHeq {u} {w} {w'} {A1} {A2} eqta exta {f} {g} e1 e2 h =
  TSQUASHeq-ext-eq (λ a b q → exta a b w' e1 e2 q) h


irr-tsquash : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → TSQUASHeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' f g
                                 → (z : w ⊑· w') → TSQUASHeq (eqInType u w' (eqta w' z)) w' f g)
irr-tsquash u w A1 A2 eqta exta f g w1 e1 w' e' h z = irr-TSQUASHeq eqta exta (⊑-trans· e1 e') z h
{--  ca , a1 , a2 , isv₁ , isv₂ , c₁ , c₂ , eqa'
  where
    eqa' : eqInType u w' (eqta w' z) a1 a2
    eqa' = exta a1 a2 w' (⊑-trans· e1 e') z eqa--}


irr-lift : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
           (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 A2))
           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
           (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
           → ∀𝕎 w1 (λ w' e' → eqInType (↓U u) w' (eqta w' (⊑-trans· e1 e')) f g
                              → (z : w ⊑· w') → eqInType (↓U u) w' (eqta w' z) f g)
irr-lift u w A1 A2 eqta exta f g w1 e1 w' e' eqi z = exta f g w' (⊑-trans· e1 e') z eqi


irr-ffdefs : (u : univs) (w : 𝕎·) (x1 A1 A2 : CTerm)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → FFDEFSeq x1 (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' f g
                                 → (z : w ⊑· w') → FFDEFSeq x1 (eqInType u w' (eqta w' z)) w' f g)
irr-ffdefs u w x1 A1 A2 eqta exta f g w1 e1 w' e' (x2 , eqa , nd) z =
  x2 , eqa' , nd
  where
    eqa' : eqInType u w' (eqta w' z) x1 x2
    eqa' = exta x1 x2 w' (⊑-trans· e1 e') z eqa



tsp→ext : {u : univs} {w : 𝕎·} {A B : CTerm} {eqt : eqTypes u w A B}
           → TSP eqt → eqInTypeExt eqt
tsp→ext {u} {w} {A} {B} {eqt} tsp eqt' a b = TSP.extl1 tsp B eqt' a b , TSP.extrevl1 tsp B eqt' a b



∀𝕎-tsp→ext : {u : univs} {w : 𝕎·} {A B : CTerm} {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A B)}
                → ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1))
                → ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
∀𝕎-tsp→ext {u} {w} {A} {B} {eqta} aw w1 e1 = tsp→ext (aw w1 e1)



∀𝕎-fam-tsp→ext : {u : univs} {w : 𝕎·} {A1 : CTerm} {B1 : CTerm0} {A2 : CTerm} {B2 : CTerm0}
                    {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
                    {eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                           → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2))}
                    → ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → TSP (eqtb w1 e1 a1 a2 ea))
                    → ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
∀𝕎-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} aw w1 e1 a1 a2 eqa = tsp→ext (aw w1 e1 a1 a2 eqa)




eqTypes-eqInTypeExt : {u : univs} {w : 𝕎·} {A B : CTerm} (eqt1 eqt2 : eqTypes u w A B)
                      → eqInTypeExt eqt1
                      → eqInTypeExt eqt2
eqTypes-eqInTypeExt {u} {w} {A} {B} eqt1 eqt2 ext eqt' a b =
  (λ eqi → fst h1 (snd h2 eqi)) , λ eqi → fst h2 (snd h1 eqi)
  where
    h1 : (eqInType u w eqt1 a b → eqInType u w eqt' a b) × (eqInType u w eqt' a b → eqInType u w eqt1 a b)
    h1 = ext eqt' a b

    h2 : (eqInType u w eqt1 a b → eqInType u w eqt2 a b) × (eqInType u w eqt2 a b → eqInType u w eqt1 a b)
    h2 = ext eqt2 a b





wPredExtIrr-eqInType-mon : {u : univs} {w : 𝕎·} {A B : CTerm}
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A B))
                           (ext : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqta w₁ e) a b))
                           (w1 : 𝕎·) (e1 : w ⊑· w1)
                           → (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (∀𝕎-mon e1 eqta w₁ e) a b)
wPredExtIrr-eqInType-mon {u} {w} {A} {B} eqta ext w1 e1 a b w' ea eb ei = ext a b w' (⊑-trans· e1 ea) (⊑-trans· e1 eb) ei




wPredDepExtIrr-eqInType-mon : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (eqtb w₁ e a b x₂) c d))
                              (w1 : 𝕎·) (e1 : w ⊑· w1)
                              → (a b c d : CTerm) → wPredDepExtIrr (λ w' e' z → eqInType u w' (∀𝕎-mon e1 eqtb w' e' a b z) c d)
wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1 a b c d w' ea eb xa xb ei =
  extb a b c d w' (⊑-trans· e1 ea) (⊑-trans· e1 eb) xa xb ei



is-uni→eqTypes : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
                  (eqt : eqTypes u w A B)
                  → eqTypes (uni (fst u)) w A B
is-uni→eqTypes {u} isu {w} {A} {B} eqt rewrite isu = eqt




is-uni→eqInType : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm} {a b : CTerm}
                   (eqt : eqTypes u w A B)
                   (eqi : eqInType u w eqt a b)
                   → Σ (eqTypes (uni (fst u)) w A B) (λ z → eqInType (uni (fst u)) w z a b)
is-uni→eqInType {u} isu {w} {A} {B} {a} {b} eqt eqi rewrite isu = eqt , eqi
\end{code}
