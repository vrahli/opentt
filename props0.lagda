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

module props0 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
              (EC : Encode)
       where
       --(bar : Bar W) where
open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]

≡CTerm→equalInTypeₗ : {u : ℕ} {w : 𝕎·} {A a a' b : CTerm}
                      → a ≡ a'
                      → equalInType u w A a b
                      → equalInType u w A a' b
≡CTerm→equalInTypeₗ {u} {w} {A} {a} {a'} {b} e z rewrite e = z



≡CTerm→equalInTypeᵣ : {u : ℕ} {w : 𝕎·} {A a b b' : CTerm}
                      → b ≡ b'
                      → equalInType u w A a b
                      → equalInType u w A a b'
≡CTerm→equalInTypeᵣ {u} {w} {A} {a} {b} {b'} e z rewrite e = z



≡CTerm→∈Type : {u : ℕ} {w : 𝕎·} {A a a' : CTerm}
                      → a ≡ a'
                      → ∈Type u w A a
                      → ∈Type u w A a'
≡CTerm→∈Type {u} {w} {A} {a} {a'} e z rewrite e = z



-- MOVE to mod
∀𝕎-□Func2 : {w : 𝕎·} {f g h : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e')
                       → □· w f
                       → □· w g
                       → □· w h
∀𝕎-□Func2 {w} {f} {g} {h} aw a b = Mod.□Func M (Mod.∀𝕎-□Func M aw a) b


-- MOVE to mod
∀𝕎-□Func3 : {w : 𝕎·} {f g h k : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e' → k w' e')
                       → □· w f
                       → □· w g
                       → □· w h
                       → □· w k
∀𝕎-□Func3 {w} {f} {g} {h} aw a b c = Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□Func M aw a) b) c


-- MOVE to mod
∀𝕎-□Func4 : {w : 𝕎·} {f g h k j : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e' → k w' e' → j w' e')
                       → □· w f
                       → □· w g
                       → □· w h
                       → □· w k
                       → □· w j
∀𝕎-□Func4 {w} {f} {g} {h} aw a b c d = Mod.□Func M (Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□Func M aw a) b) c) d


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
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTTNAT x x₁) = ⊥-elim (NATneqTNAT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTFREE x x₁) = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (NATneqISECT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (NATneqTUNION (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSQUASH A1 A2 x x₁ eqtA) = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTTRUNC A1 A2 x x₁ eqtA) = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTNORWITE A1 A2 x x₁ eqtA) = ⊥-elim (NATneqNOWRITE (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSUBSING A1 A2 x x₁ eqtA) = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt c₁ x))
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
eqTypes-pres-eqInType u w A B a b (EQTTNAT x x₁) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTFREE x x₁) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTTRUNC A1 A2 x x₁ eqtA) e = {!!}
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
eqTypes-mon u {A} {B} {w1} (EQTTNAT x x₁) w2 ext = EQTTNAT (⇛-mon ext x) (⇛-mon ext x₁)
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

eqTypes-mon u {A} {B} {w1} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) w2 ext =
  EQTW A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqta) (∀𝕎-mon ext eqtb) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqta w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b a₀ b₀ : CTerm) → wPredDepExtIrr (λ w e x₂ → eqInType u w (∀𝕎-mon ext eqtb w e a b x₂) a₀ b₀)
    extb' a b a₀ b₀ w' e1 e2 x1 x2 ei = extb a b a₀ b₀ w' (⊑-trans· ext e1) (⊑-trans· ext e2) x1 x2 ei

eqTypes-mon u {A} {B} {w1} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) w2 ext =
  EQTM A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqta) (∀𝕎-mon ext eqtb) exta' extb'
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

eqTypes-mon u {A} {B} {w1} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) w2 ext =
  EQTISECT A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) (∀𝕎-mon ext eqtB) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtB w e) a b)
    extb' a b w' e1 e2 ei = extb a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) w2 ext =
  EQTTUNION A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqta) (∀𝕎-mon ext eqtb) exta' extb'
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

{-eqTypes-mon u {A} {B} {w1} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) w2 ext =
  EQTQTUNION A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) (∀𝕎-mon ext eqtB) exta' extb'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

    extb' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtB w e) a b)
    extb' a b w' e1 e2 ei = extb a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei-}

eqTypes-mon u {A} {B} {w1} (EQTSQUASH A1 A2 x x₁ eqtA exta) w2 ext =
  EQTSQUASH A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

{-eqTypes-mon u {A} {B} {w1} (EQTTRUNC A1 A2 x x₁ eqtA exta) w2 ext =
  EQTTRUNC A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei-}

eqTypes-mon u {A} {B} {w1} (EQTNOWRITE A1 A2 x x₁ eqtA exta) w2 ext =
  EQTNOWRITE A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTNOREAD A1 A2 x x₁ eqtA exta) w2 ext =
  EQTNOREAD A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTSUBSING A1 A2 x x₁ eqtA exta) w2 ext =
  EQTSUBSING A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

{--
eqTypes-mon u {A} {B} {w1} (EQTDUM A1 A2 x x₁ {--eqtA--}) w2 ext =
  EQTDUM A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) {--(eqTypes-mon u {A1} {A2} {w1} eqtA w2 ext)--}
--}

{--
eqTypes-mon u {A} {B} {w1} (EQTDUM A1 A2 x x₁ eqtA exta) w2 ext =
  EQTDUM A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei
--}

eqTypes-mon u {A} {B} {w1} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) w2 ext =
  EQFFDEFS A1 A2 x1 x2 (⇛-mon ext x) (⇛-mon ext x₁) (∀𝕎-mon ext eqtA) exta' (∀𝕎-mon ext eqx)
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTPURE x x₁) w2 ext =
  EQTPURE (⇛-mon ext x) (⇛-mon ext x₁)

eqTypes-mon u {A} {B} {w1} (EQTNOSEQ x x₁) w2 ext =
  EQTNOSEQ (⇛-mon ext x) (⇛-mon ext x₁)

eqTypes-mon u {A} {B} {w1} (EQTTERM t1 t2 c₁ c₂ x) w2 ext =
  EQTTERM t1 t2 (⇛-mon ext c₁) (⇛-mon ext c₂) (Mod.↑□ M x ext)

eqTypes-mon u {A} {B} {w1} (EQTUNIV i p c₁ c₂) w2 ext = EQTUNIV i p (⇛-mon ext c₁) (⇛-mon ext c₂) --(m x w2 ext)

eqTypes-mon u {A} {B} {w1} (EQTLIFT A1 A2 c₁ c₂ eqtA exta) w2 ext =
  EQTLIFT A1 A2 (⇛-mon ext c₁) (⇛-mon ext c₂) (∀𝕎-mon ext eqtA) exta'
  where
    exta' : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (∀𝕎-mon ext eqtA w e) a b)
    exta' a b w' e1 e2 ei = exta a b w' (⊑-trans· ext e1) (⊑-trans· ext e2) ei

eqTypes-mon u {A} {B} {w1} (EQTBAR x) w2 ext = EQTBAR (Mod.↑□ M x ext)



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



□·-⇛!sameℕ-sym : {w : 𝕎·} {a b : Term}
                        → □· w (λ w' _ → ⇛!sameℕ w' a b)
                        → □· w (λ w' _ → ⇛!sameℕ w' b a)
□·-⇛!sameℕ-sym {w} {a} {b} h =
  Mod.∀𝕎-□Func M (λ w1 e1 → ⇛!sameℕ-sym) h




□·-⇛!sameℕ-trans : {w : 𝕎·} {a b c : Term}
                          → □· w (λ w' _ → ⇛!sameℕ w' a b)
                          → □· w (λ w' _ → ⇛!sameℕ w' b c)
                          → □· w (λ w' _ → ⇛!sameℕ w' a c)
□·-⇛!sameℕ-trans {w} {a} {b} {c} h₁ h₂ =
  Mod.□Func M (Mod.∀𝕎-□Func M aw h₁) h₂
  where
    aw : ∀𝕎 w (λ w' e' → ⇛!sameℕ w' a b → ⇛!sameℕ w' b c → ⇛!sameℕ w' a c)
    aw w1 e1 = ⇛!sameℕ-trans



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


⇓∼ℕ-sym : {w : 𝕎·} {a b : Term}
             → ⇓∼ℕ w a b
             → ⇓∼ℕ w b a
⇓∼ℕ-sym {w} {a} {b} (n , w' , c1 , c2) = n , w' , c2 , c1



⇓-from-to→≡𝕎 : {w1 w2 w3 : 𝕎·} {t u v : Term}
                 → isValue u
                 → isValue v
                 → t ⇓ u from w1 to w2
                 → t ⇓ v from w1 to w3
                 → u ≡ v × w2 ≡ w3
⇓-from-to→≡𝕎 {w1} {w2} {w3} {t} {u} {v} isvu isvv (n , comp1) (m , comp2) with n ≤? m
... | yes p rewrite steps-val-det w1 w2 w3 t u v n m isvu comp1 comp2 p
                  | steps-val-det-𝕎 w1 w2 w3 t u v n m isvu comp1 comp2 p = refl , refl
... | no p rewrite steps-val-det w1 w3 w2 t v u m n isvv comp2 comp1 (≰⇒≥ p)
                 | steps-val-det-𝕎 w1 w3 w2 t v u m n isvv comp2 comp1 (≰⇒≥ p) = refl , refl


⇓-from-to≡wᵣ : {a b : Term} {w1 w2 w3 : 𝕎·}
               → w2 ≡ w3
               → a ⇓ b from w1 to w2
               → a ⇓ b from w1 to w3
⇓-from-to≡wᵣ {a} {b} {w1} {w2} {w3} eqw comp rewrite eqw = comp



⇓-from-to≡wₗ : {a b : Term} {w1 w2 w3 : 𝕎·}
               → w1 ≡ w2
               → a ⇓ b from w1 to w3
               → a ⇓ b from w2 to w3
⇓-from-to≡wₗ {a} {b} {w1} {w2} {w3} eqw comp rewrite eqw = comp


⇓∼ℕ-trans : {w : 𝕎·} {a b c : Term}
             → ⇓∼ℕ w a b
             → ⇓∼ℕ w b c
             → ⇓∼ℕ w a c
⇓∼ℕ-trans {w} {a} {b} {c} (n , w1 , c1 , c2) (m , w2 , d1 , d2)
  rewrite fst (⇓-from-to→≡𝕎 {w} {w1} {w2} {b} {NUM n} {NUM m} tt tt c2 d1)
        | snd (⇓-from-to→≡𝕎 {w} {w1} {w2} {b} {NUM n} {NUM m} tt tt c2 d1) =
  m , w2 , c1 , d2


TNATeq-sym : {w : 𝕎·} {a b : CTerm}
             → TNATeq w a b
             → TNATeq w b a
TNATeq-sym {w} {a} {b} h w1 e1 = lift (⇓∼ℕ-sym (lower (h w1 e1)))


TNATeq-trans : {w : 𝕎·} {a b c : CTerm}
             → TNATeq w a b
             → TNATeq w b c
             → TNATeq w a c
TNATeq-trans {w} {a} {b} {c} h q w1 e1 = lift (⇓∼ℕ-trans (lower (h w1 e1)) (lower (q w1 e1)))


□TNATeq-sym : {w : 𝕎·} {a b : CTerm}
                        → □· w (λ w' _ → TNATeq w' a b)
                        → □· w (λ w' _ → TNATeq w' b a)
□TNATeq-sym {w} {a} {b} h =
  Mod.∀𝕎-□Func M (λ w1 e1 → TNATeq-sym {w1} {a} {b}) h


□TNATeq-trans : {w : 𝕎·} {a b c : CTerm}
                        → □· w (λ w' _ → TNATeq w' a b)
                        → □· w (λ w' _ → TNATeq w' b c)
                        → □· w (λ w' _ → TNATeq w' a c)
□TNATeq-trans {w} {a} {b} {c} h₁ h₂ =
  Mod.□Func M (Mod.∀𝕎-□Func M aw h₁) h₂
  where
    aw : ∀𝕎 w (λ w' e' → TNATeq w' a b → TNATeq w' b c → TNATeq w' a c)
    aw w1 e1 = TNATeq-trans {w1} {a} {b} {c}


□NATeq-sym : {w : 𝕎·} {a b : CTerm}
                        → □· w (λ w' _ → NATeq w' a b)
                        → □· w (λ w' _ → NATeq w' b a)
□NATeq-sym {w} {a} {b} h =
  Mod.∀𝕎-□Func M (λ w1 e1 → strongMonEq-sym) h



□NATeq-trans : {w : 𝕎·} {a b c : CTerm}
                → □· w (λ w' _ → NATeq w' a b)
                → □· w (λ w' _ → NATeq w' b c)
                → □· w (λ w' _ → NATeq w' a c)
□NATeq-trans {w} {a} {b} {c} h₁ h₂ =
  Mod.□Func M (Mod.∀𝕎-□Func M aw h₁) h₂
  where
    aw : ∀𝕎 w (λ w' e' → NATeq w' a b → NATeq w' b c → NATeq w' a c)
    aw w1 e1 = strongMonEq-trans



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
eqTypes⇛NAT {u} {w} {A} {B} (EQTTNAT x x₁) comp = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) comp = ⊥-elim (NATneqLT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) comp = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTFREE x x₁) comp = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqPI (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqSET (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) comp = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) comp = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) comp = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA exta) comp = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTTRUNC A1 A2 x x₁ eqtA exta) comp = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} (EQTNOWRITE A1 A2 x x₁ eqtA exta) comp = ⊥-elim (NATneqNOWRITE (⇛-val-det tt tt comp x))
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


PIeq-ext-eq : {eqa1 eqa2 : per}
              {eqb1 : (a b : CTerm) → eqa1 a b → per}
              {eqb2 : (a b : CTerm) → eqa2 a b → per}
              {t1 t2 : CTerm}
              → ((a b : CTerm) → eqa2 a b → eqa1 a b)
              → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb1 a b ea1 f g → eqb2 a b ea2 f g)
              → PIeq eqa1 eqb1 t1 t2
              → PIeq eqa2 eqb2 t1 t2
PIeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {t1} {t2} exta extb e a b a∈ =
  extb (#APPLY t1 a) (#APPLY t2 b) a b (exta a b a∈) a∈ (e a b (exta a b a∈))


SUMeq-ext-eq : {eqa1 eqa2 : per}
               {eqb1 : (a b : CTerm) → eqa1 a b → per}
               {eqb2 : (a b : CTerm) → eqa2 a b → per}
               {w : 𝕎·} {t1 t2 : CTerm}
               → ((a b : CTerm) → eqa1 a b → eqa2 a b)
               → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb1 a b ea1 f g → eqb2 a b ea2 f g)
               → SUMeq eqa1 eqb1 w t1 t2
               → SUMeq eqa2 eqb2 w t1 t2
SUMeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb (a1 , a2 , b1 , b2 , a∈ , c₁ , c₂ , b∈) =
  a1 , a2 , b1 , b2 , exta a1 a2 a∈ , c₁ , c₂ , extb b1 b2 a1 a2 a∈ (exta a1 a2 a∈) b∈


SETeq-ext-eq : {eqa1 eqa2 : per}
               {eqb1 : (a b : CTerm) → eqa1 a b → per}
               {eqb2 : (a b : CTerm) → eqa2 a b → per}
               {t1 t2 : CTerm}
               → ((a b : CTerm) → eqa1 a b → eqa2 a b)
               → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb1 a b ea1 f g → eqb2 a b ea2 f g)
               → SETeq eqa1 eqb1 t1 t2
               → SETeq eqa2 eqb2 t1 t2
SETeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {t1} {t2} exta extb (b , a∈ , b∈) =
  b , exta t1 t2 a∈ , extb b b t1 t2 a∈ (exta t1 t2 a∈) b∈


weq-ext-eq : {eqa1 eqa2 : per}
             {eqb1 : (a b : CTerm) → eqa1 a b → per}
             {eqb2 : (a b : CTerm) → eqa2 a b → per}
             {w : 𝕎·} {t1 t2 : CTerm}
             → ((a b : CTerm) → eqa1 a b → eqa2 a b)
             → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb2 a b ea2 f g → eqb1 a b ea1 f g)
             → weq eqa1 eqb1 w t1 t2
             → weq eqa2 eqb2 w t1 t2
weq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb (weqC a1 f1 a2 f2 e c1 c2 q) =
  weqC
    a1 f1 a2 f2 (exta a1 a2 e) c1 c2
    (λ b1 b2 eb → weq-ext-eq exta extb (q b1 b2 (extb b1 b2 a1 a2 e (exta a1 a2 e) eb)))



meq-ext-eq : {eqa1 eqa2 : per}
             {eqb1 : (a b : CTerm) → eqa1 a b → per}
             {eqb2 : (a b : CTerm) → eqa2 a b → per}
             {w : 𝕎·} {t1 t2 : CTerm}
             → ((a b : CTerm) → eqa1 a b → eqa2 a b)
             → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb2 a b ea2 f g → eqb1 a b ea1 f g)
             → meq eqa1 eqb1 w t1 t2
             → meq eqa2 eqb2 w t1 t2
meq.meqC (meq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb h) with meq.meqC h
... | (a1 , f1 , a2 , f2 , e , c1 , c2 , f) =
  a1 , f1 , a2 , f2 , exta a1 a2 e , c1 , c2 ,
  λ b1 b2 eb → meq-ext-eq exta extb (f b1 b2 (extb b1 b2 a1 a2 e (exta a1 a2 e) eb))


irr-fam-w : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → weq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) w' f g
                                  → (z : w ⊑· w') → weq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) w' f g)
irr-fam-w u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' q z =
  weq-ext-eq
    (λ a b e → exta a b w' (⊑-trans· e1 e') z e)
    (λ f1 f2 a1 a2 ex ey e → extb a1 a2 f1 f2 w' z (⊑-trans· e1 e') ey ex e)
    q



irr-fam-m : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → meq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) w' f g
                                  → (z : w ⊑· w') → meq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) w' f g)
irr-fam-m u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' q z =
  meq-ext-eq
    (λ a b e → exta a b w' (⊑-trans· e1 e') z e)
    (λ f1 f2 a1 a2 ex ey e → extb a1 a2 f1 f2 w' z (⊑-trans· e1 e') ey ex e)
    q


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



-----------------------
data TUNION-eq (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t1 t2 : CTerm) : Set(lsuc(L))
data TUNION-eq eqa eqb t1 t2 where
  TUNION-eq-base : (a1 a2 : CTerm) (ea : eqa a1 a2) (eb : eqb a1 a2 ea t1 t2) → TUNION-eq eqa eqb t1 t2
  TUNION-eq-trans : (t : CTerm) → TUNION-eq eqa eqb t1 t → TUNION-eq eqa eqb t t2 → TUNION-eq eqa eqb t1 t2


→TUNION-eq : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {t1 t2 : CTerm}
               → TUNIONeq eqa eqb t1 t2
               → TUNION-eq eqa eqb t1 t2
→TUNION-eq {eqa} {eqb} {t1} {t2} (0 , a1 , a2 , ea , eb) = TUNION-eq-base a1 a2 ea eb
→TUNION-eq {eqa} {eqb} {t1} {t2} (suc n , t , (a1 , a2 , ea , eb) , q) =
  TUNION-eq-trans t (TUNION-eq-base a1 a2 ea eb) (→TUNION-eq (n , q))



TUNIONeqℕ-trans : {n m : ℕ} {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {t1 t2 t3 : CTerm}
                 → TUNIONeqℕ n eqa eqb t1 t2
                 → TUNIONeqℕ m eqa eqb t2 t3
                 → TUNIONeqℕ (n + suc m) eqa eqb t1 t3
TUNIONeqℕ-trans {0} {m} {eqa} {eqb} {t1} {t2} {t3} h q = t2 , h , q
TUNIONeqℕ-trans {suc n} {m} {eqa} {eqb} {t1} {t2} {t3} (t , h0 , h1) q = t , h0 , TUNIONeqℕ-trans h1 q



TUNIONeq-trans : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {t1 t2 t3 : CTerm}
                 → TUNIONeq eqa eqb t1 t2
                 → TUNIONeq eqa eqb t2 t3
                 → TUNIONeq eqa eqb t1 t3
TUNIONeq-trans {eqa} {eqb} {t1} {t2} {t3} (n , h) (m , q) = n + suc m , TUNIONeqℕ-trans h q



TUNION-eq→ : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {t1 t2 : CTerm}
               → TUNION-eq eqa eqb t1 t2
               → TUNIONeq eqa eqb t1 t2
TUNION-eq→ {eqa} {eqb} {t1} {t2} (TUNION-eq-base a1 a2 ea eb) = 0 , a1 , a2 , ea , eb
TUNION-eq→ {eqa} {eqb} {t1} {t2} (TUNION-eq-trans t h1 h2) = TUNIONeq-trans (TUNION-eq→ h1) (TUNION-eq→ h2)


TUNION-eq-sym : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → ((f g : CTerm) (a b : CTerm) (ea1 : eqa a b) (ea2 : eqa b a) → eqb a b ea1 f g → eqb b a ea2 g f)
                 → TUNION-eq eqa eqb t1 t2
                 → TUNION-eq eqa eqb t2 t1
TUNION-eq-sym {eqa} {eqb} {t1} {t2} syma symb (TUNION-eq-base a1 a2 ea eb) =
  TUNION-eq-base a2 a1 (syma a1 a2 ea) (symb t1 t2 a1 a2 ea (syma a1 a2 ea) eb)
TUNION-eq-sym {eqa} {eqb} {t1} {t2} syma symb (TUNION-eq-trans t h1 h2) =
  TUNION-eq-trans t (TUNION-eq-sym syma symb h2) (TUNION-eq-sym syma symb h1)



TUNIONeq-sym : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → ((f g : CTerm) (a b : CTerm) (ea1 : eqa a b) (ea2 : eqa b a) → eqb a b ea1 f g → eqb b a ea2 g f)
                 → TUNIONeq eqa eqb t1 t2
                 → TUNIONeq eqa eqb t2 t1
TUNIONeq-sym {eqa} {eqb} {t1} {t2} syma symb h = TUNION-eq→ (TUNION-eq-sym syma symb (→TUNION-eq h))



{--
→TUNIONeqℕ-suc : {n : ℕ} {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {t1 t2 : CTerm} (t : CTerm)
                    → TUNIONeqℕ n eqa w t1 t
                    → TUNIONeqBase eqa w t t2
                    → TUNIONeqℕ (suc n) eqa w t1 t2
→TUNIONeqℕ-suc {0} {eqa} {w} {t1} {t2} t h q = t , h , q
→TUNIONeqℕ-suc {suc n} {eqa} {w} {t1} {t2} t (t0 , h0 , h1) q = t0 , h0 , →TUNIONeqℕ-suc {n} t h1 q
--}


TUNION-eq-ext-eq : {eqa1 eqa2 : per}
                   {eqb1 : (a b : CTerm) → eqa1 a b → per} {eqb2 : (a b : CTerm) → eqa2 a b → per} {t1 t2 : CTerm}
                   → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                   → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb1 a b ea1 f g → eqb2 a b ea2 f g)
                   → TUNION-eq eqa1 eqb1 t1 t2
                   → TUNION-eq eqa2 eqb2 t1 t2
TUNION-eq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {t1} {t2} exta extb (TUNION-eq-base a1 a2 ea eb) =
  TUNION-eq-base a1 a2 (exta a1 a2 ea) (extb t1 t2 a1 a2 ea (exta a1 a2 ea) eb)
TUNION-eq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {t1} {t2} exta extb (TUNION-eq-trans t h1 h2) =
  TUNION-eq-trans t (TUNION-eq-ext-eq exta extb h1) (TUNION-eq-ext-eq exta extb h2)



TUNIONeq-ext-eq : {eqa1 eqa2 : per}
                  {eqb1 : (a b : CTerm) → eqa1 a b → per} {eqb2 : (a b : CTerm) → eqa2 a b → per}
                  {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → ((f g : CTerm) (a b : CTerm) (ea1 : eqa1 a b) (ea2 : eqa2 a b) → eqb1 a b ea1 f g → eqb2 a b ea2 f g)
                  → TUNIONeq eqa1 eqb1 t1 t2
                  → TUNIONeq eqa2 eqb2 t1 t2
TUNIONeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {t1} {t2} exta extb h = TUNION-eq→ (TUNION-eq-ext-eq exta extb (→TUNION-eq h))



irr-TUNIONeq : {u : univs} {w w' : 𝕎·} {A1 : CTerm} {B1 : CTerm0} {A2 : CTerm} {B2 : CTerm0}
               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
               (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
               (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
               {f g : CTerm}
               (e1 e2 : w ⊑· w')
               → TUNIONeq (eqInType u w' (eqta w' e1)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e1 a1 a2 eqa)) f g
               → TUNIONeq (eqInType u w' (eqta w' e2)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e2 a1 a2 eqa)) f g
irr-TUNIONeq {u} {w} {w'} {A1} {B1} {A2} {B2} eqta eqtb exta extb {f} {g} e1 e2 h =
  TUNIONeq-ext-eq (λ a b q → exta a b w' e1 e2 q) (λ f₁ g₁ a b ea1 ea2 q → extb a b f₁ g₁ w' e1 e2 ea1 ea2 q) h
-----------------



irr-fam-tunion-eq : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                    (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                    (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
                    → ∀𝕎 w1 (λ w' e' → TUNION-eq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) f g
                                       → (z : w ⊑· w') → TUNION-eq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) f g)
irr-fam-tunion-eq u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' (TUNION-eq-base a1 a2 ea eb) z =
  TUNION-eq-base
    a1 a2
    (exta a1 a2 w' (⊑-trans· e1 e') z ea)
    (extb a1 a2 f g w' (⊑-trans· e1 e') z ea (exta a1 a2 w' (⊑-trans· e1 e') z ea) eb)
irr-fam-tunion-eq u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' (TUNION-eq-trans t h h₁) z =
  TUNION-eq-trans
    t
    (irr-fam-tunion-eq u w A1 B1 A2 B2 eqta eqtb exta extb f t w1 e1 w' e' h z)
    (irr-fam-tunion-eq u w A1 B1 A2 B2 eqta eqtb exta extb t g w1 e1 w' e' h₁ z)



irr-fam-tunion : (u : univs) (w : 𝕎·) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                 (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                 (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                      → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                 (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                 (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                 (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
                 → ∀𝕎 w1 (λ w' e' → TUNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa)) f g
                                    → (z : w ⊑· w') → TUNIONeq (eqInType u w' (eqta w' z)) (λ a1 a2 eqa → eqInType u w' (eqtb w' z a1 a2 eqa)) f g)
irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' h z =
  TUNION-eq→ (irr-fam-tunion-eq u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1 w' e' (→TUNION-eq h) z)



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


ISECTeq-ext-eq : {eqa1 eqa2 eqb1 eqb2 : per} {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → ((a b : CTerm) → eqb1 a b → eqb2 a b)
                  → ISECTeq eqa1 eqb1 t1 t2
                  → ISECTeq eqa2 eqb2 t1 t2
ISECTeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {t1} {t2} exta extb (u , v) = exta t1 t2 u , extb t1 t2 v


irr-isect : (u : univs) (w : 𝕎·) (A1 A2 B1 B2 : CTerm)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
            → ∀𝕎 w1 (λ w' e' → ISECTeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) f g
                                → (z : w ⊑· w') → ISECTeq (eqInType u w' (eqta w' z)) (eqInType u w' (eqtb w' z)) f g)
irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1 w' e' (eqa , eqb) z =
  eqa' , eqb'
  where
    eqa' : eqInType u w' (eqta w' z) f g
    eqa' = exta f g w' (⊑-trans· e1 e') z eqa

    eqb' : eqInType u w' (eqtb w' z) f g
    eqb' = extb f g w' (⊑-trans· e1 e') z eqb


UNIONeq-ext-eq : {eqa1 eqa2 eqb1 eqb2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → ((a b : CTerm) → eqb1 a b → eqb2 a b)
                  → UNIONeq eqa1 eqb1 w t1 t2
                  → UNIONeq eqa2 eqb2 w t1 t2
UNIONeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , exta a b z)
UNIONeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , extb a b z)


QTUNIONeq-ext-eq : {eqa1 eqa2 eqb1 eqb2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → ((a b : CTerm) → eqb1 a b → eqb2 a b)
                  → QTUNIONeq eqa1 eqb1 w t1 t2
                  → QTUNIONeq eqa2 eqb2 w t1 t2
QTUNIONeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , exta a b z)
QTUNIONeq-ext-eq {eqa1} {eqa2} {eqb1} {eqb2} {w} {t1} {t2} exta extb (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , extb a b z)


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



irr-qtunion : (u : univs) (w : 𝕎·) (A1 A2 B1 B2 : CTerm)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
            → ∀𝕎 w1 (λ w' e' → QTUNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) w' f g
                                → (z : w ⊑· w') → QTUNIONeq (eqInType u w' (eqta w' z)) (eqInType u w' (eqtb w' z)) w' f g)
irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1 w' e' (a , b , inj₁ (c₁ , c₂ , eqa)) z =
  a , b , inj₁ (c₁ , c₂ , eqa')
  where
    eqa' : eqInType u w' (eqta w' z) a b
    eqa' = exta a b w' (⊑-trans· e1 e') z eqa
irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1 w' e' (a , b , inj₂ (c₁ , c₂ , eqb)) z =
  a , b , inj₂ (c₁ , c₂ , eqb')
  where
    eqb' : eqInType u w' (eqtb w' z) a b
    eqb' = extb a b w' (⊑-trans· e1 e') z eqb



data TSQUASH-eq (eqa : per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
data TSQUASH-eq eqa w t1 t2 where
  TSQUASH-eq-base : (a1 a2 : CTerm) → #isValue a1 → #isValue a2 → ∼C! w t1 a1 → ∼C! w t2 a2 → eqa a1 a2 → TSQUASH-eq eqa w t1 t2
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
TSQUASHeq-ext-eq {eqa1} {eqa2} {w} {t1} {t2} ext h = TSQUASH-eq→ (TSQUASH-eq-ext-eq ext (→TSQUASH-eq h))



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



data TTRUNC-eq (eqa : per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
data TTRUNC-eq eqa w t1 t2 where
  TTRUNC-eq-base : (a1 a2 : CTerm) → #isValue a1 → #isValue a2 → t1 #⇓ a1 at w → t2 #⇓ a2 at w → eqa a1 a2 → TTRUNC-eq eqa w t1 t2
  TTRUNC-eq-trans : (t : CTerm) → TTRUNC-eq eqa w t1 t → TTRUNC-eq eqa w t t2 → TTRUNC-eq eqa w t1 t2


→TTRUNC-eq : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
               → TTRUNCeq eqa w t1 t2
               → TTRUNC-eq eqa w t1 t2
→TTRUNC-eq {eqa} {w} {t1} {t2} (0 , a1 , a2 , i1 , i2 , c1 , c2 , ea) = TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea
→TTRUNC-eq {eqa} {w} {t1} {t2} (suc n , t , (a1 , a2 , i1 , i2 , c1 , c2 , ea) , q) =
  TTRUNC-eq-trans t (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) (→TTRUNC-eq (n , q))




TTRUNCeqℕ-trans : {n m : ℕ} {eqa : per} {w : 𝕎·} {t1 t2 t3 : CTerm}
                 → TTRUNCeqℕ n eqa w t1 t2
                 → TTRUNCeqℕ m eqa w t2 t3
                 → TTRUNCeqℕ (n + suc m) eqa w t1 t3
TTRUNCeqℕ-trans {0} {m} {eqa} {w} {t1} {t2} {t3} h q = t2 , h , q
TTRUNCeqℕ-trans {suc n} {m} {eqa} {w} {t1} {t2} {t3} (t , h0 , h1) q = t , h0 , TTRUNCeqℕ-trans h1 q


TTRUNCeq-trans : {eqa : per} {w : 𝕎·} {t1 t2 t3 : CTerm}
                 → TTRUNCeq eqa w t1 t2
                 → TTRUNCeq eqa w t2 t3
                 → TTRUNCeq eqa w t1 t3
TTRUNCeq-trans {eqa} {w} {t1} {t2} {t3} (n , h) (m , q) = n + suc m , TTRUNCeqℕ-trans h q



TTRUNC-eq→ : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
               → TTRUNC-eq eqa w t1 t2
               → TTRUNCeq eqa w t1 t2
TTRUNC-eq→ {eqa} {w} {t1} {t2} (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 a) = 0 , a1 , a2 , i1 , i2 , c1 , c2 , a
TTRUNC-eq→ {eqa} {w} {t1} {t2} (TTRUNC-eq-trans t h1 h2) = TTRUNCeq-trans (TTRUNC-eq→ h1) (TTRUNC-eq→ h2)


TTRUNC-eq-sym : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → TTRUNC-eq eqa w t1 t2
                 → TTRUNC-eq eqa w t2 t1
TTRUNC-eq-sym {eqa} {w} {t1} {t2} sym (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) = TTRUNC-eq-base a2 a1 i2 i1 c2 c1 (sym a1 a2 ea)
TTRUNC-eq-sym {eqa} {w} {t1} {t2} sym (TTRUNC-eq-trans t h1 h2) =
  TTRUNC-eq-trans t (TTRUNC-eq-sym sym h2) (TTRUNC-eq-sym sym h1)



TTRUNCeq-sym : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → TTRUNCeq eqa w t1 t2
                 → TTRUNCeq eqa w t2 t1
TTRUNCeq-sym {eqa} {w} {t1} {t2} sym h = TTRUNC-eq→ (TTRUNC-eq-sym sym (→TTRUNC-eq h))



→TTRUNCeqℕ-suc : {n : ℕ} {eqa : per} {w : 𝕎·} {t1 t2 : CTerm} (t : CTerm)
                    → TTRUNCeqℕ n eqa w t1 t
                    → TTRUNCeqBase eqa w t t2
                    → TTRUNCeqℕ (suc n) eqa w t1 t2
→TTRUNCeqℕ-suc {0} {eqa} {w} {t1} {t2} t h q = t , h , q
→TTRUNCeqℕ-suc {suc n} {eqa} {w} {t1} {t2} t (t0 , h0 , h1) q = t0 , h0 , →TTRUNCeqℕ-suc {n} t h1 q



TTRUNC-eq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                 → TTRUNC-eq eqa1 w t1 t2
                 → TTRUNC-eq eqa2 w t1 t2
TTRUNC-eq-ext-eq {eqa} {w} {t1} {t2} ext (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) =
  TTRUNC-eq-base a1 a2 i1 i2 c1 c2 (ext a1 a2 ea)
TTRUNC-eq-ext-eq {eqa} {w} {t1} {t2} ext (TTRUNC-eq-trans t h1 h2) =
  TTRUNC-eq-trans t (TTRUNC-eq-ext-eq ext h1) (TTRUNC-eq-ext-eq ext h2)



TTRUNCeq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                 → TTRUNCeq eqa1 w t1 t2
                 → TTRUNCeq eqa2 w t1 t2
TTRUNCeq-ext-eq {eqa1} {eqa2} {w} {t1} {t2} ext h = TTRUNC-eq→ (TTRUNC-eq-ext-eq ext (→TTRUNC-eq h))



irr-TTRUNCeq : {u : univs} {w w' : 𝕎·} {A1 A2 : CTerm}
                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                {f g : CTerm}
                (e1 e2 : w ⊑· w')
                → TTRUNCeq (eqInType u w' (eqta w' e1)) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e2)) w' f g
irr-TTRUNCeq {u} {w} {w'} {A1} {A2} eqta exta {f} {g} e1 e2 h =
  TTRUNCeq-ext-eq (λ a b q → exta a b w' e1 e2 q) h


irr-ttrunc : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' f g
                                 → (z : w ⊑· w') → TTRUNCeq (eqInType u w' (eqta w' z)) w' f g)
irr-ttrunc u w A1 A2 eqta exta f g w1 e1 w' e' h z = irr-TTRUNCeq eqta exta (⊑-trans· e1 e') z h



NOWRITEeq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → NOWRITEeq eqa1 w t1 t2
                  → NOWRITEeq eqa2 w t1 t2
NOWRITEeq-ext-eq {eqa1} {eqa2} {w} {t1} {t2} ext (h , c₁ , c₂) = ext t1 t2 h , c₁ , c₂


irr-NOWRITEeq : {u : univs} {w w' : 𝕎·} {A1 A2 : CTerm}
               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
               {f g : CTerm}
               (e1 e2 : w ⊑· w')
               → NOWRITEeq (eqInType u w' (eqta w' e1)) w' f g
               → NOWRITEeq (eqInType u w' (eqta w' e2)) w' f g
irr-NOWRITEeq {u} {w} {w'} {A1} {A2} eqta exta {f} {g} e1 e2 h =
  NOWRITEeq-ext-eq (λ a b q → exta a b w' e1 e2 q) h


irr-nowrite : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → NOWRITEeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' f g
                                 → (z : w ⊑· w') → NOWRITEeq (eqInType u w' (eqta w' z)) w' f g)
irr-nowrite u w A1 A2 eqta exta f g w1 e1 w' e' h z = irr-NOWRITEeq eqta exta (⊑-trans· e1 e') z h
{--  ca , a1 , a2 , isv₁ , isv₂ , c₁ , c₂ , eqa'
  where
    eqa' : eqInType u w' (eqta w' z) a1 a2
    eqa' = exta a1 a2 w' (⊑-trans· e1 e') z eqa--}



NOREADeq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → NOREADeq eqa1 w t1 t2
                  → NOREADeq eqa2 w t1 t2
NOREADeq-ext-eq {eqa1} {eqa2} {w} {t1} {t2} ext (h , c₁ , c₂) = ext t1 t2 h , c₁ , c₂


irr-NOREADeq : {u : univs} {w w' : 𝕎·} {A1 A2 : CTerm}
               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
               {f g : CTerm}
               (e1 e2 : w ⊑· w')
               → NOREADeq (eqInType u w' (eqta w' e1)) w' f g
               → NOREADeq (eqInType u w' (eqta w' e2)) w' f g
irr-NOREADeq {u} {w} {w'} {A1} {A2} eqta exta {f} {g} e1 e2 h =
  NOREADeq-ext-eq (λ a b q → exta a b w' e1 e2 q) h


irr-noread : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → NOREADeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' f g
                                 → (z : w ⊑· w') → NOREADeq (eqInType u w' (eqta w' z)) w' f g)
irr-noread u w A1 A2 eqta exta f g w1 e1 w' e' h z = irr-NOREADeq eqta exta (⊑-trans· e1 e') z h
{--  ca , a1 , a2 , isv₁ , isv₂ , c₁ , c₂ , eqa'
  where
    eqa' : eqInType u w' (eqta w' z) a1 a2
    eqa' = exta a1 a2 w' (⊑-trans· e1 e') z eqa--}



SUBSINGeq-ext-eq : {eqa1 eqa2 : per} {t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → SUBSINGeq eqa1 t1 t2
                  → SUBSINGeq eqa2 t1 t2
SUBSINGeq-ext-eq {eqa1} {eqa2} {t1} {t2} ext (h , q) = ext t1 t1 h , ext t2 t2 q


irr-SUBSINGeq : {u : univs} {w w' : 𝕎·} {A1 A2 : CTerm}
               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
               {f g : CTerm}
               (e1 e2 : w ⊑· w')
               → SUBSINGeq (eqInType u w' (eqta w' e1)) f g
               → SUBSINGeq (eqInType u w' (eqta w' e2)) f g
irr-SUBSINGeq {u} {w} {w'} {A1} {A2} eqta exta {f} {g} e1 e2 h =
  SUBSINGeq-ext-eq (λ a b q → exta a b w' e1 e2 q) h


irr-subsing : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
              → ∀𝕎 w1 (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) f g
                                 → (z : w ⊑· w') → SUBSINGeq (eqInType u w' (eqta w' z)) f g)
irr-subsing u w A1 A2 eqta exta f g w1 e1 w' e' h z = irr-SUBSINGeq eqta exta (⊑-trans· e1 e') z h


irr-lift : (u : univs) (w : 𝕎·) (A1 A2 : CTerm)
           (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 A2))
           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
           (f g : CTerm) (w1 : 𝕎·) (e1 : w ⊑· w1)
           → ∀𝕎 w1 (λ w' e' → eqInType (↓U u) w' (eqta w' (⊑-trans· e1 e')) f g
                              → (z : w ⊑· w') → eqInType (↓U u) w' (eqta w' z) f g)
irr-lift u w A1 A2 eqta exta f g w1 e1 w' e' eqi z = exta f g w' (⊑-trans· e1 e') z eqi




FFDEFSeq-ext-eq : {w : 𝕎·} {eqa1 eqa2 : per} {x t1 t2 : CTerm}
                  → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                  → FFDEFSeq x eqa1 w t1 t2
                  → FFDEFSeq x eqa2 w t1 t2
FFDEFSeq-ext-eq {w} {eqa1} {eqa2} {x} {t1} {t2} ext (y , h , q) = y , ext x y h , q



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



NOWRITEeq-sym : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → NOWRITEeq eqa w t1 t2
                 → NOWRITEeq eqa w t2 t1
NOWRITEeq-sym {eqa} {w} {t1} {t2} sym (h , c₁ , c₂) = sym t1 t2 h , c₂ , c₁


NOWRITEeq-trans : {eqa : per} {w : 𝕎·} {t1 t2 t3 : CTerm}
                 → ((a b c : CTerm) → eqa a b → eqa b c → eqa a c)
                 → NOWRITEeq eqa w t1 t2
                 → NOWRITEeq eqa w t2 t3
                 → NOWRITEeq eqa w t1 t3
NOWRITEeq-trans {eqa} {w} {t1} {t2} {t3} trans (h , c₁ , c₂) (q , c₃ , c₄) = trans t1 t2 t3 h q , c₁ , c₄



NOREADeq-sym : {eqa : per} {w : 𝕎·} {t1 t2 : CTerm}
                 → ((a b : CTerm) → eqa a b → eqa b a)
                 → NOREADeq eqa w t1 t2
                 → NOREADeq eqa w t2 t1
NOREADeq-sym {eqa} {w} {t1} {t2} sym (h , c₁ , c₂) = sym t1 t2 h , c₂ , c₁


NOREADeq-trans : {eqa : per} {w : 𝕎·} {t1 t2 t3 : CTerm}
                 → ((a b c : CTerm) → eqa a b → eqa b c → eqa a c)
                 → NOREADeq eqa w t1 t2
                 → NOREADeq eqa w t2 t3
                 → NOREADeq eqa w t1 t3
NOREADeq-trans {eqa} {w} {t1} {t2} {t3} trans (h , c₁ , c₂) (q , c₃ , c₄) = trans t1 t2 t3 h q , c₁ , c₄


SUBSINGeq-sym : {eqa : per} {t1 t2 : CTerm}
                 → SUBSINGeq eqa t1 t2
                 → SUBSINGeq eqa t2 t1
SUBSINGeq-sym {eqa} {t1} {t2} (h , q) = q , h


SUBSINGeq-trans : {eqa : per} {t1 t2 t3 : CTerm}
                 → SUBSINGeq eqa t1 t2
                 → SUBSINGeq eqa t2 t3
                 → SUBSINGeq eqa t1 t3
SUBSINGeq-trans {eqa} {t1} {t2} {t3} (h , q) (r , s) = h , s


→≡eqTypes : {i : univs} {w : 𝕎·} {a1 a2 b1 b2 : CTerm}
                → a1 ≡ a2
                → b1 ≡ b2
                → eqTypes i w a1 b1
                → eqTypes i w a2 b2
→≡eqTypes {i} {w} {a1} {a2} {b1} {b2} e1 e2 h rewrite e1 | e2 = h


→≡eqTypesSub0 : {i : univs} {w : 𝕎·} {a1 a2 b1 b2 : CTerm0} {x y : CTerm}
                → a1 ≡ a2
                → b1 ≡ b2
                → eqTypes i w (sub0 x a1) (sub0 y b1)
                → eqTypes i w (sub0 x a2) (sub0 y b2)
→≡eqTypesSub0 {i} {w} {a1} {a2} {b1} {b2} {x} {y} e1 e2 h rewrite e1 | e2 = h


→≡eqInType : {i : univs} {w : 𝕎·} {A B C D a b : CTerm} (eqt : eqTypes i w A C)
              (e1 : A ≡ B) (e2 : C ≡ D)
           → eqInType i w eqt a b
           → eqInType i w (→≡eqTypes e1 e2 eqt) a b
→≡eqInType {i} {w} {A} {B} {C} {D} {a} {b} eqt e1 e2 ei rewrite e1 | e2 = ei

→≡eqInType-rev : {i : univs} {w : 𝕎·} {A B C D a b : CTerm} (eqt : eqTypes i w A C)
                 (e1 : A ≡ B) (e2 : C ≡ D)
                 → eqInType i w (→≡eqTypes e1 e2 eqt) a b
                 → eqInType i w eqt a b
→≡eqInType-rev {i} {w} {A} {B} {C} {D} {a} {b} eqt e1 e2 ei rewrite e1 | e2 = ei

\end{code}
