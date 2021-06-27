\begin{code}

open import bar

module props0 (bar : Bar) where

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
open import calculus
open import world
open import theory (bar)
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]
impliesEqTypes : (u : ℕ) {w : world} {A B : Term} → equalTypes u w A B → eqtypes w A B
impliesEqTypes u e = (u , e)

impliesEqInType : (u : ℕ) {w : world} {T a b : Term} → equalInType u w T a b → eqintype w T a b
impliesEqInType u f = (u , f)

univInBar : (n : ℕ) (w : world) → eqUnivi n w (UNIV n) (UNIV n)
univInBar n w =  Bar.allW-inBar inOpenBar-Bar λ w1 e1 → compAllRefl (UNIV n) w1 , compAllRefl (UNIV n) w1

lemma1 : (w : world) → equalTypes 0 w (UNIV 0) (UNIV 0)
lemma1 w = EQTUNIV (univInBar 0 w)

lemma2 : (w : world) → eqtypes w (UNIV 0) (UNIV 0)
lemma2 w = impliesEqTypes 0 (lemma1 w)

lemma3 : (w : world) → equalTypes 1 w (UNIV 1) (UNIV 1)
lemma3 w = EQTUNIV (univInBar 1 w)

lemma4 : (w : world) → eqtypes w (UNIV 1) (UNIV 1)
lemma4 w = impliesEqTypes 1 (lemma3 w)

lemma5 : (w : world) → equalInType 1 w (UNIV 1) (UNIV 0) (UNIV 0)
lemma5 w = (lemma3 w , inj₁ (EQTUNIV (univInBar 0 w)))

lemma6 : (w : world) → eqintype w (UNIV 1) (UNIV 0) (UNIV 0)
lemma6 w = impliesEqInType 1 (lemma5 w)


-- EQ
EQinj1 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → a ≡ d
EQinj1 refl =  refl

EQinj2 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → b ≡ e
EQinj2 refl =  refl

EQinj3 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → c ≡ f
EQinj3 refl =  refl


EQneqNAT : {t a b : Term} → ¬ (EQ t a b) ≡ NAT
EQneqNAT {t} {a} {b} ()

EQneqQNAT : {t a b : Term} → ¬ (EQ t a b) ≡ QNAT
EQneqQNAT {t} {a} {b} ()

EQneqLT : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ LT c d
EQneqLT {t} {a} {b} {c} {d} ()

EQneqQLT : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ QLT c d
EQneqQLT {t} {a} {b} {c} {d} ()

EQneqFREE : {t a b : Term} → ¬ (EQ t a b) ≡ FREE
EQneqFREE {t} {a} {b} ()

EQneqPI : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ PI c d
EQneqPI {t} {a} {b} {c} {d} ()

EQneqSUM : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ SUM c d
EQneqSUM {t} {a} {b} {c} {d} ()

EQneqSET : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ SET c d
EQneqSET {t} {a} {b} {c} {d} ()

EQneqUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ UNION c d
EQneqUNION {t} {a} {b} {c} {d} ()

EQneqTSQUASH : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TSQUASH c
EQneqTSQUASH {t} {a} {b} {c} ()

EQneqFFDEFS : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ FFDEFS c d
EQneqFFDEFS {t} {a} {b} {c} {d} ()

EQneqLOWER : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ LOWER c
EQneqLOWER {t} {a} {b} {c} ()

EQneqSHRINK : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ SHRINK c
EQneqSHRINK {t} {a} {b} {c} ()

EQneqUNIV : {t a b : Term} {n : ℕ} → ¬ (EQ t a b) ≡ UNIV n
EQneqUNIV {t} {a} {b} {n} ()



-- PI
PIinj1 : {a b c d : Term} → PI a b ≡ PI c d → a ≡ c
PIinj1 refl =  refl

PIinj2 : {a b c d : Term} → PI a b ≡ PI c d → b ≡ d
PIinj2 refl =  refl

PIneqNAT : {a b : Term} → ¬ (PI a b) ≡ NAT
PIneqNAT {a} {b} ()

PIneqQNAT : {a b : Term} → ¬ (PI a b) ≡ QNAT
PIneqQNAT {a} {b} ()

PIneqLT : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ LT c d
PIneqLT {a} {b} {c} {d} ()

PIneqQLT : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ QLT c d
PIneqQLT {a} {b} {c} {d} ()

PIneqFREE : {a b : Term} → ¬ (PI a b) ≡ FREE
PIneqFREE {a} {b} ()

PIneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (PI a b) ≡ EQ c d e
PIneqEQ {a} {b} {c} {d} {e} ()

PIneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ SUM c d
PIneqSUM {a} {b} {c} {d} ()

PIneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ SET c d
PIneqSET {a} {b} {c} {d} ()

PIneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ UNION c d
PIneqUNION {a} {b} {c} {d} ()

PIneqTSQUASH : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TSQUASH c
PIneqTSQUASH {a} {b} {c} ()

PIneqFFDEFS : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ FFDEFS c d
PIneqFFDEFS {a} {b} {c} {d} ()

PIneqLOWER : {a b : Term} {c : Term} → ¬ (PI a b) ≡ LOWER c
PIneqLOWER {a} {b} {c} ()

PIneqSHRINK : {a b : Term} {c : Term} → ¬ (PI a b) ≡ SHRINK c
PIneqSHRINK {a} {b} {c} ()

PIneqUNIV : {a b : Term} {n : ℕ} → ¬ (PI a b) ≡ UNIV n
PIneqUNIV {a} {b} {n} ()


wPredExtIrr-× : {w : world} {f g : wPred w} → wPredExtIrr f → wPredExtIrr g → wPredExtIrr (λ w' e' → f w' e' × g w' e')
wPredExtIrr-× {w} {f} {g} wF wG w' e1 e2 (hf , hg) = wF w' e1 e2 hf , wG w' e1 e2 hg


wPredExtIrr-⇛ : {w : world} {a b : Term} → wPredExtIrr {w} (λ w' e' → a ⇛ b at w')
wPredExtIrr-⇛ {w} {a} {b} w' e1 e2 h = h


≤-Σ+ : {n m : ℕ} → n ≤ m → Σ ℕ (λ k → m ≡ n + k)
≤-Σ+ {0} {m} _≤_.z≤n = (m , refl)
≤-Σ+ {suc n} {suc m} (_≤_.s≤s le) with ≤-Σ+ le
... | (k , p) rewrite p = k , refl


step≡nothing-steps : (w : world) (a : Term) (n : ℕ) → step a w ≡ nothing → steps n a w ≡ a
step≡nothing-steps w a 0 h = refl
step≡nothing-steps w a (suc n) h rewrite h = refl


steps-+ : (n m : ℕ) (a : Term) (w : world) → steps (n + m) a w ≡ steps m (steps n a w) w
steps-+ 0 m a w = refl
steps-+ (suc n) m a w with step⊎ a w
... | inj₁ (u , p) rewrite p = steps-+ n m u w
... | inj₂ p rewrite p rewrite step≡nothing-steps w a m p = refl


steps-val-det : (w : world) (a v₁ v₂ : Term) (n m : ℕ) → isValue v₁ → steps n a w ≡ v₁ → steps m a w ≡ v₂ → n ≤ m → v₁ ≡ v₂
steps-val-det w a v₁ v₂ n m isv₁ c₁ c₂ p with ≤-Σ+ p
... | (k , q) rewrite q | steps-+ n k a w | c₂ | c₁ | stepsVal v₁ w k isv₁ = c₂


⇓-val-det : (w : world) (a v₁ v₂ : Term) → isValue v₁ → isValue v₂ → a ⇓ v₁ at w → a ⇓ v₂ at w → v₁ ≡ v₂
⇓-val-det w a v₁ v₂ isv₁ isv₂ (n , c₁) (m , c₂) with n ≤? m
... | yes p = steps-val-det w a v₁ v₂ n m isv₁ c₁ c₂ p
... | no p = sym (steps-val-det w a v₂ v₁ m n isv₂ c₂ c₁ (≰⇒≥ p))


⇛-val-det : {w : world} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇛ v₁ at w → a ⇛ v₂ at w → v₁ ≡ v₂
⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ =
  ⇓-val-det w a v₁ v₂ isv₁ isv₂ h1 h2
  where
    h1 : a ⇓ v₁ at w
    h1 = let c = c₁ w (extRefl w) in Level.lower c

    h2 : a ⇓ v₂ at w
    h2 = let c = c₂ w (extRefl w) in Level.lower c


-- NAT
NATneqQNAT : ¬ NAT ≡ QNAT
NATneqQNAT ()

NATneqLT : {c d : Term} → ¬ NAT ≡ LT c d
NATneqLT {c} {d} ()

NATneqQLT : {c d : Term} → ¬ NAT ≡ QLT c d
NATneqQLT {c} {d} ()

NATneqFREE : ¬ NAT ≡ FREE
NATneqFREE ()

NATneqPI : {c : Term} {d : Term} → ¬ NAT ≡ PI c d
NATneqPI {c} {d} ()

NATneqSUM : {c : Term} {d : Term} → ¬ NAT ≡ SUM c d
NATneqSUM {c} {d} ()

NATneqSET : {c : Term} {d : Term} → ¬ NAT ≡ SET c d
NATneqSET {c} {d} ()

NATneqUNION : {c : Term} {d : Term} → ¬ NAT ≡ UNION c d
NATneqUNION {c} {d} ()

NATneqEQ : {c d e : Term} → ¬ NAT ≡ EQ c d e
NATneqEQ {c} {d} {e} ()

NATneqTSQUASH : {c : Term} → ¬ NAT ≡ TSQUASH c
NATneqTSQUASH {c} ()

NATneqFFDEFS : {c d : Term} → ¬ NAT ≡ FFDEFS c d
NATneqFFDEFS {c} {d} ()

NATneqLOWER : {c : Term} → ¬ NAT ≡ LOWER c
NATneqLOWER {c} ()

NATneqSHRINK : {c : Term} → ¬ NAT ≡ SHRINK c
NATneqSHRINK {c} ()

NATneqUNIV : {n : ℕ} → ¬ NAT ≡ UNIV n
NATneqUNIV {n} ()

is-universe : (u : univs) → Set₁
is-universe u =
  (w : world) (T1 T2 : Term)
  → fst (snd u) w T1 T2
  → inbar w (λ w' _ → T1 ⇛ (UNIV (fst u)) at w' × T2 ⇛ (UNIV (fst u)) at w')


lift⊥ : Lift {0ℓ} 1ℓ ⊥ → ⊥
lift⊥ ()


eqTypes-pres-eqInType-NAT : (u : univs) (isu : is-universe u) (w : world) (A B a b : Term)
                            → A ⇛ NAT at w
                            → B ⇛ NAT at w
                            → inbar w (λ w' _ → strongMonEq w' a b)
                            → (eqt2 : eqTypes u w A B) → eqInType u w eqt2 a b
--{-# INLINE allW-inOpenBar-inOpenBar' #-}
{-# TERMINATING #-} -- inlining [Bar.allW-inBar-inBar' inOpenBar-Bar] works: uncomment c
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTNAT x x₁) = e
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTQNAT x x₁) = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTFREE x x₁) = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTSQUASH A1 A2 x x₁ eqtA) = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTUNIV x) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))
eqTypes-pres-eqInType-NAT u isu w A B a b c₁ c₂ e (EQTBAR x) = c
  where
    c2 : allW w (λ w' e' → (x : eqTypes u w' A B) → eqInType u w' x a b)
    c2 w2 e2 e' = eqTypes-pres-eqInType-NAT u isu w2 A B a b (⇛-mon e2 c₁) (⇛-mon e2 c₂) (inOpenBar-mon e2 e) e'

    loc-allW-inOpenBar-inOpenBar' : (i : inOpenBar w (λ w' _ → eqTypes u w' A B)) → inOpenBar' w i (λ w' _ x → eqInType u w' x a b)
    loc-allW-inOpenBar-inOpenBar' i w1 e1 = w2 , extRefl w2 , λ w3 e3 z → c2 w3 z (h0 w3 (extTrans e3 (extRefl w2)) z)
      where
        w2 : world
        w2 = fst (i w1 e1)

        e2 : w2 ≽ w1
        e2 = fst (snd (i w1 e1))

        h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → eqTypes u w3 A B)
        h0 = snd (snd (i w1 e1))

    c : inbar' w x (λ w' _ (x : eqTypes u w' A B) → eqInType u w' x a b)
    -- Agda's termination checker fails on this, but accepts the one above, even though, they are exactly the same up to unfolding
    c = Bar.allW-inBar-inBar' inOpenBar-Bar c2 x
    --c = loc-allW-inOpenBar-inOpenBar' x



{--
eqTypes-pres-eqInType : (u : univs) (w : world) (A B a b : Term) (eqt1 : eqTypes u w A B)
                        → eqInType u w eqt1 a b
                        → (eqt2 : eqTypes u w A B) → eqInType u w eqt2 a b
eqTypes-pres-eqInType u w A B a b (EQTNAT x x₁) e eqt2 = eqTypes-pres-eqInType-NAT u w A B a b x x₁ e eqt2
eqTypes-pres-eqInType u w A B a b (EQTQNAT x x₁) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTFREE x x₁) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTUNIV x) e = {!!}
eqTypes-pres-eqInType u w A B a b (EQTBAR x) e = {!!}--}


{--wPredExtIrr-eqInType : {w : world} {u : univs} {A B a b : Term} (eqtA : allW w (λ w' _ → eqTypes u w' A B))
                       → wPredExtIrr (λ w' e → eqInType u w' (eqtA w' e) a b)
wPredExtIrr-eqInType {w} {u} {A} {B} {a} {b} eqtA w' e1 e2 h = {!!}--}


wPredExtIrr-equalInType : {w : world} {u : ℕ} {A a b : Term}
                          → wPredExtIrr {w} (λ w' e → equalInType u w' A a b)
wPredExtIrr-equalInType {w} {u} {A} {a} {b} w' e1 e2 h = h


wPredExtIrr-const : {w : world} {F : world → Set₁}
                    → wPredExtIrr {w} (λ w' e → F w')
wPredExtIrr-const {w} {F} w' e1 e2 h = h


-- Monotonicity
mon : (p : wper) → Set₁
mon p = {a b : Term} {w : world} → p w a b → allW w (λ w' e' → p w' a b)


strongMonEq-mon : mon strongMonEq
strongMonEq-mon {a} {b} {w} (n , c₁ , c₂) w1 e1 = (n , ⇛-mon e1 c₁ , ⇛-mon e1 c₂)


weakMonEq-mon : mon weakMonEq
weakMonEq-mon {a} {b} {w} h w' e' = allW-mon e' h


eqTypes-mon : (u : univs) → mon (proj₁ (proj₂ u)) → mon (eqTypes u)
eqTypes-mon u m {A} {B} {w1} (EQTNAT x x₁) w2 ext = EQTNAT (⇛-mon ext x) (⇛-mon ext x₁)
eqTypes-mon u m {A} {B} {w1} (EQTQNAT x x₁) w2 ext = EQTQNAT (⇛-mon ext x) (⇛-mon ext x₁)
eqTypes-mon u m {A} {B} {w1} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) w2 ext =
  EQTLT a1 a2 b1 b2
    (⇛-mon ext x) (⇛-mon ext x₁)
    (strongMonEq-mon x₂ w2 ext)
    (strongMonEq-mon x₃ w2 ext)
eqTypes-mon u m {A} {B} {w1} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) w2 ext =
  EQTQLT a1 a2 b1 b2
    (⇛-mon ext x) (⇛-mon ext x₁)
    (weakMonEq-mon x₂ w2 ext)
    (weakMonEq-mon x₃ w2 ext)
eqTypes-mon u m {A} {B} {w1} (EQTFREE x x₁) w2 ext =
  EQTFREE (⇛-mon ext x) (⇛-mon ext x₁)
eqTypes-mon u m {A} {B} {w1} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) w2 ext =
  EQTPI A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (allW-mon ext eqta) (allW-mon ext eqtb)
eqTypes-mon u m {A} {B} {w1} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) w2 ext =
  EQTSUM A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (allW-mon ext eqta) (allW-mon ext eqtb)
eqTypes-mon u m {A} {B} {w1} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) w2 ext =
  EQTSET A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (allW-mon ext eqta) (allW-mon ext eqtb)
eqTypes-mon u m {A} {B} {w1} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) w2 ext =
  EQTEQ a1 b1 a2 b2 A₁ B₁ (⇛-mon ext x) (⇛-mon ext x₁)
    (allW-mon ext eqtA) (allW-mon ext eqt1) (allW-mon ext eqt2)
eqTypes-mon u m {A} {B} {w1} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) w2 ext =
  EQTUNION A1 B1 A2 B2 (⇛-mon ext x) (⇛-mon ext x₁) (allW-mon ext eqtA) (allW-mon ext eqtB)
eqTypes-mon u m {A} {B} {w1} (EQTSQUASH A1 A2 x x₁ eqtA) w2 ext =
  EQTSQUASH A1 A2 (⇛-mon ext x) (⇛-mon ext x₁) (allW-mon ext eqtA)
eqTypes-mon u m {A} {B} {w1} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) w2 ext =
  EQFFDEFS A1 A2 x1 x2 (⇛-mon ext x) (⇛-mon ext x₁) (allW-mon ext eqtA) (allW-mon ext eqx)
eqTypes-mon u m {A} {B} {w1} (EQTUNIV x) w2 ext = EQTUNIV (m x w2 ext)
eqTypes-mon u m {A} {B} {w1} (EQTBAR x) w2 ext = EQTBAR (Bar.inBar-mon inOpenBar-Bar ext x)



if-equalInType-EQ : (u : ℕ) (w : world) (T a b t₁ t₂ : Term)
                    → equalInType u w (EQ a b T) t₁ t₂
                    → inbar w (λ w' e' → t₁ ⇛ AX at w' × t₂ ⇛ AX at w' × equalInType u w' T a b)
{-# INLINE allW-inOpenBar'-inOpenBar #-}
if-equalInType-EQ u w T a b t₁ t₂ (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (EQneqPI (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (EQneqSET (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi)
  rewrite EQinj1 (compAllVal x tt)  | EQinj2 (compAllVal x tt)  | EQinj3 (compAllVal x tt)
        | EQinj1 (compAllVal x₁ tt) | EQinj2 (compAllVal x₁ tt) | EQinj3 (compAllVal x₁ tt) =
  Bar.allW-inBarFunc
    inOpenBar-Bar
    (λ w1 e1 (c₁ , c₂ , eqi1) → c₁ , c₂ , eqtA w1 e1 , eqi1)
    eqi
if-equalInType-EQ u w T a b t₁ t₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTUNIV x , eqi) = Bar.allW-inBarFunc inOpenBar-Bar z2 x
  where
    z2 : allW w (λ w' e' → ((EQ a b T) ⇛ (UNIV u) at w' × (EQ a b T) ⇛ (UNIV u) at w') → t₁ ⇛ AX at w' × t₂ ⇛ AX at w' × equalInType u w' T a b)
    z2 w' e' (c₁ , c₂) = ⊥-elim (EQneqUNIV (compAllVal c₁ tt))
if-equalInType-EQ u w T a b t₁ t₂ (EQTBAR x , eqi) =
  Bar.inBar-idem
    inOpenBar-Bar
    (wPredExtIrr-× wPredExtIrr-⇛ (wPredExtIrr-× wPredExtIrr-⇛ wPredExtIrr-equalInType))
    (Bar.allW-inBar'-inBar
      inOpenBar-Bar
      {w}
      {λ w' e' → eqTypes (uni u) w' (EQ a b T) (EQ a b T)}
      {λ w' e' x → eqInType (uni u) w' x t₁ t₂}
      (λ w1 e1 eqt1 eqi1 → if-equalInType-EQ u w1 T a b t₁ t₂ (eqt1 , eqi1))
      x
      eqi)


strongMonEq-sym : {w : world} {a b : Term}
                  → strongMonEq w a b
                  → strongMonEq w b a
strongMonEq-sym {w} {a} {b} (n , c₁ , c₂) = n , c₂ , c₁


inbar-strongMonEq-sym : {w : world} {a b : Term}
                        → inbar w (λ w' _ → strongMonEq w' a b)
                        → inbar w (λ w' _ → strongMonEq w' b a)
inbar-strongMonEq-sym {w} {a} {b} h =
  Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 → strongMonEq-sym) h


NUMinj : {n m : ℕ} → NUM n ≡ NUM m → n ≡ m
NUMinj refl =  refl


strongMonEq-trans : {w : world} {a b c : Term}
                    → strongMonEq w a b
                    → strongMonEq w b c
                    → strongMonEq w a c
strongMonEq-trans {w} {a} {b} {c} (n , c₁ , c₂) (m , d₁ , d₂) rewrite NUMinj (⇛-val-det tt tt d₁ c₂) = n , c₁ , d₂


inbar-strongMonEq-trans : {w : world} {a b c : Term}
                          → inbar w (λ w' _ → strongMonEq w' a b)
                          → inbar w (λ w' _ → strongMonEq w' b c)
                          → inbar w (λ w' _ → strongMonEq w' a c)
inbar-strongMonEq-trans {w} {a} {b} {c} h₁ h₂ =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar h h₁) h₂
  where
    aw : allW w (λ w' e' → strongMonEq w' a b → strongMonEq w' b c → strongMonEq w' a c)
    aw w1 e1 = strongMonEq-trans

    h : inbar w (λ w' e' → strongMonEq w' a b → strongMonEq w' b c → strongMonEq w' a c)
    h = Bar.allW-inBar inOpenBar-Bar aw


weakMonEq-sym : {w : world} {a b : Term}
                → weakMonEq w a b
                → weakMonEq w b a
weakMonEq-sym {w} {a} {b} h w1 e1 = lift (fst z₂ , snd (snd z₂) , fst (snd z₂))
  where
    z₁ : Lift 1ℓ (Σ ℕ (λ n → a ⇓ NUM n at w1 × b ⇓ NUM n at w1))
    z₁ = h w1 e1

    z₂ : Σ ℕ (λ n → a ⇓ NUM n at w1 × b ⇓ NUM n at w1)
    z₂ = lower z₁


strongMonEq-pres-⇓ : {w : world} {a1 a2 : Term} {n : ℕ}
                     → strongMonEq w a1 a2
                     → a1 ⇓ NUM n at w
                     → a2 ⇓ NUM n at w
strongMonEq-pres-⇓ {w} {a1} {a2} {n} (m , c₁ , c₂) c = z₂
  where
    z₁ : NUM n ≡ NUM m
    z₁ = ⇓-val-det w a1 (NUM n) (NUM m) tt tt c (lower (c₁ w (extRefl _)))

    z₂ : a2 ⇓ NUM n at w
    z₂ rewrite NUMinj z₁ = lower (c₂ w (extRefl _))


→inbar⇛ : {w : world} {A B : Term}
            → A ⇛ B at w
            → inbar w (λ w' _ → A ⇛ B at w')
→inbar⇛ {w} {A} {B} comp = Bar.allW-inBar inOpenBar-Bar (λ w1 e1 → ⇛-mon e1 comp)



-- we can't characerize eqt like that as it might be a tower of EQTBAR
eqTypes⇛NAT : {u : univs} {w : world} {A B : Term}
               → is-universe u
               → (eqt : eqTypes u w A B)
               → A ⇛ NAT at w
               → inbar w (λ w' _ → B ⇛ NAT at w')
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTNAT x x₁) comp = →inbar⇛ x₁
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTQNAT x x₁) comp = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) comp = ⊥-elim (NATneqLT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) comp = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTFREE x x₁) comp = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) comp = ⊥-elim (NATneqPI (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) comp = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) comp = ⊥-elim (NATneqSET (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) comp = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) comp = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTSQUASH A1 A2 x x₁ eqtA) comp = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) comp = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp x))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTUNIV x) comp =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 comp) d₁)))
eqTypes⇛NAT {u} {w} {A} {B} isu (EQTBAR x) comp = i
  where
    a : allW w (λ w' e' → eqTypes u w' A B → inbar w' (λ w'' _ → B ⇛ NAT at w''))
    a w1 e1 eqt = eqTypes⇛NAT isu eqt (⇛-mon e1 comp)

    q : wPred w
    q = λ w' _ → eqTypes u w' A B

    g : wPred w
    g = λ w' _ → inbar w' (λ w'' _ → B ⇛ NAT at w'')

    loc-allW-inOpenBarFunc : inOpenBar w q → inOpenBar w g
    loc-allW-inOpenBarFunc h w1 e1 =
      w2 , e2 , h3
      where
        h1 : exAllW w1 λ w2 e2 → (z : w2 ≽ w) → q w2 z
        h1 = h w1 e1

        w2 : world
        w2 = fst h1

        e2 : w2 ≽ w1
        e2 = fst (snd h1)

        h2 : allW w2 λ w3 e3 → (z : w3 ≽ w) → q w3 z
        h2 = snd (snd h1)

        h3 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → g w3 z)
        h3 w3 e3 z = a w3 z (h2 w3 e3 z)

    j : inbar w (λ w' _ → inbar w' (λ w'' _ → B ⇛ NAT at w''))
    j = loc-allW-inOpenBarFunc x
    --j = Bar.allW-inBarFunc inOpenBar-Bar a x

    f : wPred w
    f = λ w' _ → B ⇛ NAT at w'

    loc-inOpenBar-idem : wPredExtIrr f
                         → inOpenBar w f
    loc-inOpenBar-idem ei w1 e1 =
      fst h4 ,
      extTrans (fst (snd h4)) e2 ,
      λ w3 e3 z → ei w3 (extTrans (extTrans e3 (fst (snd h4))) (extTrans e2 e1)) z (snd (snd h4) w3 e3 (extTrans e3 (fst (snd h4))))
      where
        w2 : world
        w2 = fst (j w1 e1)

        e2 : w2 ≽ w1
        e2 = fst (snd (j w1 e1))

        h2 : allW w2 (λ w' e' → (z : w' ≽ w) → inOpenBar w' (↑wPred f z))
        h2 = snd (snd (j w1 e1))

        h3 : inOpenBar w2 (↑wPred f (extTrans e2 e1))
        h3 = h2 w2 (extRefl w2) (extTrans e2 e1)

        h4 : exAllW w2 (λ w' e' → (z : w' ≽ w2) → f w' (extTrans z (extTrans e2 e1)))
        h4 = h3 w2 (extRefl w2)

    i : inbar w (λ w' _ → B ⇛ NAT at w')
    --i = Bar.inBar-idem inOpenBar-Bar wPredExtIrr-⇛ j
    i = loc-inOpenBar-idem wPredExtIrr-⇛


eqTypesTrans : (u : univs) (w : world) (A B : Term) → Set₁
eqTypesTrans u w A B = (C : Term) → eqTypes u w B C → eqTypes u w A C

eqInTypeSym : (u : univs) {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeSym u {w} {A} {B} eqt = (a b : Term) → eqInType u w eqt a b → eqInType u w eqt b a

eqInTypeTrans : (u : univs) {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeTrans u {w} {A} {B} eqt = (a b c : Term) → eqInType u w eqt a b → eqInType u w eqt b c → eqInType u w eqt a c

eqInTypeExtL1 : {u : univs} {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeExtL1 {u} {w} {A} {B} eqt = (C : Term) (eqt' : eqTypes u w A C) (a b : Term) → eqInType u w eqt a b → eqInType u w eqt' a b

eqInTypeExtR2 : {u : univs} {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeExtR2 {u} {w} {A} {B} eqt = (C : Term) (eqt' : eqTypes u w B C) (a b : Term) → eqInType u w eqt a b → eqInType u w eqt' a b

eqInTypeExtRevL1 : {u : univs} {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeExtRevL1 {u} {w} {A} {B} eqt = (C : Term) (eqt' : eqTypes u w A C) (a b : Term) → eqInType u w eqt' a b → eqInType u w eqt a b

eqInTypeExtRevL2 : {u : univs} {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeExtRevL2 {u} {w} {A} {B} eqt = (C : Term) (eqt' : eqTypes u w C A) (a b : Term) → eqInType u w eqt' a b → eqInType u w eqt a b

eqInTypeExtRevR1 : {u : univs} {w : world} {A B : Term} (eqt : eqTypes u w A B) → Set₁
eqInTypeExtRevR1 {u} {w} {A} {B} eqt = (C : Term) (eqt' : eqTypes u w C B) (a b : Term) → eqInType u w eqt' a b → eqInType u w eqt a b

-- Type System Props
record TSP {u : univs} {w : world} {A B : Term} (eqt : eqTypes u w A B) : Set₁ where
  constructor mktsp
  field
    tsym     : eqTypes u w B A
    ttrans   : eqTypesTrans u w A B
    isym     : eqInTypeSym u eqt
    itrans   : eqInTypeTrans u eqt
    extl1    : eqInTypeExtL1 eqt
    extr2    : eqInTypeExtR2 eqt
    extrevl1 : eqInTypeExtRevL1 eqt
    extrevl2 : eqInTypeExtRevL2 eqt
    extrevr1 : eqInTypeExtRevR1 eqt


typeSysConds-NAT : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                   (x : A ⇛ NAT at w) (x₁ : B ⇛ NAT at w)
                   → TSP {u} (EQTNAT x x₁)
typeSysConds-NAT u isu w A B x x₁ =
  mktsp tsym ttrans isym itrans (iextl1 w x) (iextr2 w x) (iextrl1 w x) (iextrl2 w x) (iextrr1 w x)
  where
    tsym : eqTypes u w B A
    tsym = EQTNAT x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans C eqt1 = EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar d c)
      where
        c : inbar w (λ w' _ → C ⇛ NAT at w')
        c = eqTypes⇛NAT isu eqt1 x₁

        d : allW w (λ w' e' → C ⇛ NAT at w' → eqTypes u w' A C)
        d w1 e1 comp = EQTNAT (⇛-mon e1 x) comp

    isym : eqInTypeSym u (EQTNAT x x₁)
    isym a b eqi = inbar-strongMonEq-sym eqi

    itrans : eqInTypeTrans u (EQTNAT x x₁)
    itrans a b c eqi₁ eqi₂ = inbar-strongMonEq-trans eqi₁ eqi₂

    iextl1 : (w : world) → A ⇛ NAT at w → (C : Term) (eqt' : eqTypes u w A C) (a b : Term) → inbar w (λ w' _ → strongMonEq w' a b) → eqInType u w eqt' a b
    iextl1 w comp C (EQTNAT y y₁) a b eqi = eqi
    iextl1 w comp C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y))
    iextl1 w comp C (EQTUNIV y) a b eqi =
      ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
      where
        z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
        z = isu w A C y

        q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
        q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 comp) d₁)))

    iextl1 w comp C (EQTBAR y) a b eqi = c
      where
        aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b)
        aw w1 e1 z = iextl1 w1 (⇛-mon e1 comp) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)

        f : wPred w
        f = λ w' _ → eqTypes u w' A C

        g : wPredDep f
        g = λ w' e' (x : eqTypes u w' A C) → eqInType u w' x a b

        loc-allW-inOpenBar-inOpenBar' : (i : inOpenBar w f) → inOpenBar' w i g
        loc-allW-inOpenBar-inOpenBar' i w1 e1 = w2 , extRefl w2 , λ w3 e3 z → aw w3 z (h0 w3 (extTrans e3 (extRefl w2)) z)
          where
            w2 : world
            w2 = fst (i w1 e1)

            e2 : w2 ≽ w1
            e2 = fst (snd (i w1 e1))

            h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
            h0 = snd (snd (i w1 e1))

        c : inbar' w y (λ w' e' z → eqInType u w' z a b)
        c = loc-allW-inOpenBar-inOpenBar' y
        --c = Bar.allW-inBar-inBar' inOpenBar-Bar aw y

    iextr2 : (w : world) → A ⇛ NAT at w → (C : Term) (eqt' : eqTypes u w B C) (a b : Term) → inbar w (λ w' _ → strongMonEq w' a b) → eqInType u w eqt' a b
    iextr2 w comp C eqt' a b = {!!}

    iextrl1 : (w : world) → A ⇛ NAT at w → (C : Term) (eqt' : eqTypes u w A C) (a b : Term) → eqInType u w eqt' a b → inbar w (λ w' _ → strongMonEq w' a b)
    iextrl1 w comp C (EQTNAT y y₁) a b eqi = eqi
    iextrl1 w comp C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y))
    iextrl1 w comp C (EQTUNIV y) a b eqi =
      ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
      where
        z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
        z = isu w A C y

        q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
        q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 comp) d₁)))
    iextrl1 w comp C (EQTBAR y) a b eqi =
      Bar.inBar-idem
        inOpenBar-Bar
        wPredExtIrr-const
        (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
      where
        aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b
                             → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → strongMonEq w'' a b) e'))
        aw w1 e1 x₁ eqx₁ = iextrl1 w1 (⇛-mon e1 comp) C x₁ a b eqx₁

    iextrl2 : (w : world) → A ⇛ NAT at w → (C : Term) (eqt' : eqTypes u w C A) (a b : Term) → eqInType u w eqt' a b → inbar w (λ w' _ → strongMonEq w' a b)
    iextrl2 w comp C eqt' a b eqi = {!!}

    iextrr1 : (w : world) → A ⇛ NAT at w → (C : Term) (eqt' : eqTypes u w C B) (a b : Term) → eqInType u w eqt' a b → inbar w (λ w' _ → strongMonEq w' a b)
    iextrr1 w comp C eqt' a b eqi = {!!}


typeSysConds-PI-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                       (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : allW w (λ w1 e1 →
                                         (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypes u w B A
typeSysConds-PI-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  EQTPI A2 B2 A1 B1 x₁ x syma symb
  where
    syma : allW w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (syma w' e) a1 a2 → eqTypes u w' (sub a1 B2) (sub a2 B1))
    symb w1 e1 a b eqi = TSP.tsym (indb w1 e1 b a eqi2)
      where
        eqi1 : eqInType u w1 (eqta w1 e1) a b
        eqi1 = TSP.extrevl2 (inda w1 e1) A2 (syma w1 e1) a b eqi

        eqi2 : eqInType u w1 (eqta w1 e1) b a
        eqi2 = TSP.isym (inda w1 e1) a b eqi1


typeSysConds-PI-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypesTrans u w A B
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0)
  rewrite PIinj1 (⇛-val-det tt tt y x₁)
        | PIinj2 (⇛-val-det tt tt y x₁) =
  EQTPI A1 B1 C2 D2 x y₁ eqa eqb
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqa w' e) a1 a2 → eqTypes u w' (sub a1 B1) (sub a2 D2))
    eqb w1 e1 a1 a2 ea = TSP.ttrans (indb w1 e1 a1 a2 eqa12) (sub a2 D2) eqb2
      where
        eqa12 : eqInType u w1 (eqta w1 e1) a1 a2
        eqa12 = TSP.extrevl1 (inda w1 e1) C2 (eqa w1 e1) a1 a2 ea

        eqa22' : eqInType u w1 (eqta w1 e1) a2 a2
        eqa22' = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 eqa12) eqa12

        eqa22 : eqInType u w1 (eqta0 w1 e1) a2 a2
        eqa22 = TSP.extr2 (inda w1 e1) C2 (eqta0 w1 e1) a2 a2 eqa22'

        eqb2 : eqTypes u w1 (sub a2 B2) (sub a2 D2)
        eqb2 = eqtb0 w1 e1 a2 a2 eqa22

typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-PI-ttrans
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C eqt


typeSysConds-PI-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                       (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : allW w (λ w1 e1 →
                                         (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqInTypeSym u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                    eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
                  → (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                        eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY g a1) (APPLY f a2))
    h w1 e1 imp a1 a2 ea = TSP.isym (indb w1 e1 a1 a2 ea) (APPLY f a2) (APPLY g a1) eb
      where
        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea

        ea3 : eqInType u w1 (eqta w1 e1) a1 a1
        ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea ea2

        eib1 : eqTypes u w1 (sub a1 B1) (sub a1 B2)
        eib1 = eqtb w1 e1 a1 a1 ea3

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (APPLY f a2) (APPLY g a1)
        eb1 = imp a2 a1 ea2

        eb2 : eqInType u w1 eib1 (APPLY f a2) (APPLY g a1)
        eb2 = TSP.extrevr1 (indb w1 e1 a1 a1 ea3)
                  (sub a2 B1) (eqtb w1 e1 a2 a1 ea2) (APPLY f a2) (APPLY g a1) eb1

        eb : eqInType u w1 (eqtb w1 e1 a1 a2 ea) (APPLY f a2) (APPLY g a1)
        eb = TSP.extrevl1 (indb w1 e1 a1 a2 ea)
                 (sub a1 B2) eib1 (APPLY f a2) (APPLY g a1) eb2


typeSysConds-PI-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb a b c ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                  eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY a a1) (APPLY b a2))
                → ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                       eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY b a1) (APPLY c a2))
                → (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                      eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY a a1) (APPLY c a2))
    aw w1 e1 f g a1 a2 eqa = {!!}
      where
        --eqa1 : eqInType u w1 (eqta w1 e1) a1 a1
        --eqa1 = ?


typeSysConds-PI-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y x) -- C1≡A1
        | PIinj2 (⇛-val-det tt tt y x) -- D1≡B1
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
              → (a1 a2 : Term) (eqa : eqInType u w' (eqta0 w' e') a1 a2)
              → eqInType u w' (eqtb0 w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extl1 (indb w1 e1 a1 a2 ea1) (sub a2 B4) (eqtb0 w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a2) ef1
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl1 (inda w1 e1) A4 (eqta0 w1 e1) a1 a2 eqa

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        ef1 = imp a1 a2 ea1

typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi = {!!}


typeSysConds-PI : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                  (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 →
                                    (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextr2 iextrl1 iextrl2 iextrr1
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-PI-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    isym : eqInTypeSym u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    isym = typeSysConds-PI-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    itrans : eqInTypeTrans u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    itrans = typeSysConds-PI-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl1 : eqInTypeExtL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl1 = typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr2 : eqInTypeExtR2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr2 = {!!}

    iextrl1 : eqInTypeExtRevL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl1 = {!!}

    iextrl2 : eqInTypeExtRevL2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl2 = {!!}

    iextrr1 : eqInTypeExtRevR1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr1 = {!!}


typeSysConds : (u : univs) (isu : is-universe u) (w : world) (A B : Term) (eqt : eqTypes u w A B) → TSP eqt
typeSysConds u isu w A B (EQTNAT x x₁) = typeSysConds-NAT u isu w A B x x₁
typeSysConds u isu w A B (EQTQNAT x x₁) = {!!}
typeSysConds u isu w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
typeSysConds u isu w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
typeSysConds u isu w A B (EQTFREE x x₁) = {!!}
typeSysConds u isu w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) =
  typeSysConds-PI u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb
  where
    inda : allW w (λ w1 e1 → TSP (eqta w1 e1))
    inda w1 e1 = typeSysConds u isu w1 A1 A2 (eqta w1 e1)

    indb : allW w (λ w1 e1 →
                     (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                     → TSP (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a1 a2 ea = typeSysConds u isu w1 (sub a1 B1) (sub a2 B2) (eqtb w1 e1 a1 a2 ea)
typeSysConds u isu w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
typeSysConds u isu w A B (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
typeSysConds u isu w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) = {!!}
typeSysConds u isu w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = {!!}
typeSysConds u isu w A B (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
typeSysConds u isu w A B (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
typeSysConds u isu w A B (EQTUNIV x) = {!!}
typeSysConds u isu w A B (EQTBAR x) = {!!}


{--
-- Those need to be packaged as we did in Coq
eqTypes-sym : (u : univs) → TEQsym (eqTypes u)
eqInType-sym : (u : univs) (w : world) (A B a b : Term) (eqt : eqTypes u w A B)
               → eqInType u w eqt a b
               → eqInType u w eqt b a
eqType-refl : (u : univs) (w : world) (A B : Term)
              → eqTypes u w A B
              → eqTypes u w A A
eqInType-refl : (u : univs) (w : world) (A B a b : Term) (eqt : eqTypes u w A B)
                → eqInType u w eqt a b
                → eqInType u w eqt a a
eqType-pres-eqInType : (u : univs) (w : world) (A B C D a b : Term)
                       (eqt1 : eqTypes u w A B) (eqt2 : eqTypes u w C D)
                       → eqTypes u w B C
                       → eqInType u w eqt1 a b
                       → eqInType u w eqt2 a b
eqTypes-trans : (u : univs) (w : world) (A B C : Term) → eqTypes u w A B → eqTypes u w B C → eqTypes u w A C


eqTypes-sym u w A B (EQTNAT x x₁) = EQTNAT x₁ x
eqTypes-sym u w A B (EQTQNAT x x₁) = EQTQNAT x₁ x
eqTypes-sym u w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a2 a1 b2 b1 x₁ x (strongMonEq-sym x₂) (strongMonEq-sym x₃)
eqTypes-sym u w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a2 a1 b2 b1 x₁ x (weakMonEq-sym x₂) (weakMonEq-sym x₃)
eqTypes-sym u w A B (EQTFREE x x₁) = EQTFREE x₁ x
eqTypes-sym u w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTPI
    A2 B2 A1 B1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqta w1 e1))
    (λ w1 e1 a b eqi →
      eqTypes-sym
        u w1 (sub b B1) (sub a B2)
        (eqtb w1 e1 b a
              (eqInType-sym u w1 A1 A2 a b (eqta w1 e1)
                (eqType-pres-eqInType u w1 A2 A1 A1 A2 a b
                  (eqTypes-sym u w1 A1 A2 (eqta w1 e1))
                  (eqta w1 e1)
                  (eqType-refl u w1 A1 A2 (eqta w1 e1))
                  eqi))))
eqTypes-sym u w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTSUM
    A2 B2 A1 B1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqta w1 e1))
    (λ w1 e1 a b eqi →
      eqTypes-sym
        u w1 (sub b B1) (sub a B2)
        (eqtb w1 e1 b a
              (eqInType-sym u w1 A1 A2 a b (eqta w1 e1)
                (eqType-pres-eqInType u w1 A2 A1 A1 A2 a b
                  (eqTypes-sym u w1 A1 A2 (eqta w1 e1))
                  (eqta w1 e1)
                  (eqType-refl u w1 A1 A2 (eqta w1 e1))
                  eqi))))
eqTypes-sym u w A B (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTSET
    A2 B2 A1 B1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqta w1 e1))
    (λ w1 e1 a b eqi →
      eqTypes-sym
        u w1 (sub b B1) (sub a B2)
        (eqtb w1 e1 b a
              (eqInType-sym u w1 A1 A2 a b (eqta w1 e1)
                (eqType-pres-eqInType u w1 A2 A1 A1 A2 a b
                  (eqTypes-sym u w1 A1 A2 (eqta w1 e1))
                  (eqta w1 e1)
                  (eqType-refl u w1 A1 A2 (eqta w1 e1))
                  eqi))))
eqTypes-sym u w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) =
  EQTEQ
    b1 a1 b2 a2 B₁ A₁ x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A₁ B₁ (eqtA w1 e1))
    (λ w1 e1 → {!!}) --eqType-sym-pres-rev u w1 A₁ B₁ b1 a1 (eqtA w1 e1) (eqInType-sym u w1 A₁ B₁ a1 b1 (eqtA w1 e1) (eqt1 w1 e1)))
    (λ w1 e1 → {!!}) --eqType-sym-pres-rev u w1 A₁ B₁ b2 a2 (eqtA w1 e1) (eqInType-sym u w1 A₁ B₁ a2 b2 (eqtA w1 e1) (eqt2 w1 e1)))
eqTypes-sym u w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) =
  EQTUNION
    A2 B2 A1 B1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqtA w1 e1))
    (λ w1 e1 → eqTypes-sym u w1 B1 B2 (eqtB w1 e1))
eqTypes-sym u w A B (EQTSQUASH A1 A2 x x₁ eqtA) =
  EQTSQUASH
    A2 A1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqtA w1 e1))
eqTypes-sym u w A B (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) =
  EQFFDEFS
    A2 A1 x2 x1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqtA w1 e1))
    (λ w1 e1 → {!!}) --eqType-sym-pres-rev u w1 A1 A2 x2 x1 (eqtA w1 e1) (eqInType-sym u w1 A1 A2 x1 x2 (eqtA w1 e1) (eqx w1 e1)))
eqTypes-sym u w A B (EQTUNIV x) = {!!}
eqTypes-sym u w A B (EQTBAR x) = {!!}

eqInType-sym u w A B a b (EQTNAT x x₁) h =
  Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 → strongMonEq-sym) h
eqInType-sym u w A B a b (EQTQNAT x x₁) h =
  Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 → weakMonEq-sym) h
eqInType-sym u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) h =
  Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z → z) h
eqInType-sym u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) h = {!!}
eqInType-sym u w A B a b (EQTFREE x x₁) h = {!!}
eqInType-sym u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) h =
  Bar.allW-inBarFunc
    inOpenBar-Bar
    h₁
    h
  where
    h₁ : allW w
           (λ w' e'
             → ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) → eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY a a1) (APPLY b a2))
             → (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) → eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY b a1) (APPLY a a2))
    h₁ w1 e1 z a₁ b₁ eqa =
      eqInType-sym
        u w1 (sub a₁ B1) (sub b₁ B2) (APPLY a b₁) (APPLY b a₁)
        (eqtb w1 e1 a₁ b₁ eqa)
        (eqType-pres-eqInType u w1 (sub b₁ B1) (sub a₁ B2) (sub a₁ B1) (sub b₁ B2) (APPLY a b₁) (APPLY b a₁)
          (eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa))
          (eqtb w1 e1 a₁ b₁ eqa)
          (eqTypes-sym u w1 (sub a₁ B1) (sub a₁ B2) (eqtb w1 e1 a₁ a₁ (eqInType-refl u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa)))
          h₂)
        where
          h₂ : eqInType u w1 (eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa)) (APPLY a b₁) (APPLY b a₁)
          h₂ = z b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa)
{--      eqInType-sym
        u w1 (sub b₁ B1) (sub a₁ B2) (APPLY a b₁) (APPLY b a₁)
        {!!} --(eqtb w1 e1 b₁ a₁ (eqInType-sym-rev u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa))
        {!!}) --(z b₁ a₁ (eqInType-sym-rev u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa))) --}
eqInType-sym u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) h = {!!}
eqInType-sym u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) h = {!!}
eqInType-sym u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) h = {!!}
eqInType-sym u w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) h = {!!}
eqInType-sym u w A B a b (EQTUNIV x) h = {!!}
eqInType-sym u w A B a b (EQTBAR x) h = {!!}

eqType-refl u w A B (EQTNAT x x₁) = EQTNAT x x
eqType-refl u w A B (EQTQNAT x x₁) = {!!}
eqType-refl u w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
eqType-refl u w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
eqType-refl u w A B (EQTFREE x x₁) = {!!}
eqType-refl u w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTPI
    A1 B1 A1 B1 x x
    (λ w1 e1 → eqType-refl u w1 A1 A2 (eqta w1 e1))
    h
  where
    h : allW w (λ w' e →
         (a1 a2 : Term) → eqInType u w' (eqType-refl u w' A1 A2 (eqta w' e)) a1 a2
         → eqTypes u w' (sub a1 B1) (sub a2 B1))
    h w1 e1 a1 a2 eqa = h₀
      where
        h₃ : eqTypes u w1 A1 A1
        h₃ = eqType-refl u w1 A1 A2 (eqta w1 e1)

        h₂ : eqInType u w1 (eqta w1 e1) a1 a2
        h₂ = eqType-pres-eqInType u w1 A1 A1 A1 A2 a1 a2 (eqType-refl u w1 A1 A2 (eqta w1 e1)) (eqta w1 e1) h₃ eqa

        h₁ : eqTypes u w1 (sub a1 B1) (sub a2 B2)
        h₁ = eqtb w1 e1 a1 a2 h₂

        h₆ : eqInType u w1 (eqta w1 e1) a2 a1
        h₆ = eqInType-sym u w1 A1 A2 a1 a2 (eqta w1 e1) h₂

        h₅ : eqInType u w1 (eqta w1 e1) a2 a2
        h₅ = eqInType-refl u w1 A1 A2 a2 a1 (eqta w1 e1) h₆

        h₄ : eqTypes u w1 (sub a2 B1) (sub a2 B2)
        h₄ = eqtb w1 e1 a2 a2 h₅

        h₇ : eqTypes u w1 (sub a2 B2) (sub a2 B1)
        h₇ = eqTypes-sym u w1 (sub a2 B1) (sub a2 B2) h₄

        h₀ : eqTypes u w1 (sub a1 B1) (sub a2 B1)
        h₀ = eqTypes-trans u w1 (sub a1 B1) (sub a2 B2) (sub a2 B1) h₁ h₇


eqType-refl u w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqType-refl u w A B (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqType-refl u w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) = {!!}
eqType-refl u w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = {!!}
eqType-refl u w A B (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
eqType-refl u w A B (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
eqType-refl u w A B (EQTUNIV x) = {!!}
eqType-refl u w A B (EQTBAR x) = {!!}

eqInType-refl u w A B a b eqt h = {!!}

eqType-pres-eqInType u w A B a b eqt h = {!!}

eqTypes-trans u w A B C eqta eqtb = {!!}
--}


{--
eqInType-sym-rev u w A B a b (EQTNAT x x₁) h =
  Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 → strongMonEq-sym) h
eqInType-sym-rev u w A B a b (EQTQNAT x x₁) h =
  Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 → weakMonEq-sym) h
eqInType-sym-rev u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) h =
  Bar.allW-inBarFunc
    inOpenBar-Bar
    (λ w1 e1 (lift (n , m , c₁ , c₂ , d)) →
      lift (n , m ,
              strongMonEq-pres-⇓ (strongMonEq-sym (strongMonEq-mon x₂ w1 e1)) c₁ ,
              strongMonEq-pres-⇓ (strongMonEq-sym (strongMonEq-mon x₃ w1 e1)) c₂ ,
              d))
    h
eqInType-sym-rev u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) h = {!!}
eqInType-sym-rev u w A B a b (EQTFREE x x₁) h = {!!}
eqInType-sym-rev u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) h =
  Bar.allW-inBarFunc
    inOpenBar-Bar
    (λ w1 e1 z a₁ b₁ eqa →
      eqInType-sym-rev
        u w1 (sub b₁ B1) (sub a₁ B2) (APPLY a b₁) (APPLY b a₁)
        {!eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqa w1 e1))!} --(eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqa w1 e1)))  -- eqTypes u w1 (sub b₁ B1) (sub a₁ B2)
        {!!})
    h
eqInType-sym-rev u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym-rev u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym-rev u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) h = {!!}
eqInType-sym-rev u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) h = {!!}
eqInType-sym-rev u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) h = {!!}
eqInType-sym-rev u w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) h = {!!}
eqInType-sym-rev u w A B a b (EQTUNIV x) h = {!!}
eqInType-sym-rev u w A B a b (EQTBAR x) h = {!!}
--}


{--if-equalInType-NAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                     → equalInType u I w NAT t₁ t₂
                     → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
if-equalInType-NAT u I w t₁ t₂ (EQTNAT x x₁ , eqi) = eqi
if-equalInType-NAT u I w t₁ t₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (NATneqQNAT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (NATneqLT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (NATneqQLT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTFREE x x₁ , eqi) = ⊥-elim (NATneqFREE (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (NATneqPI (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (NATneqSUM (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (NATneqSET (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) = ⊥-elim (NATneqEQ (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (NATneqUNION (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (NATneqTSQUASH (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (NATneqFFDEFS (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , h) = x w ([]≽-refl I w) in
  let (c1 , c2) = h w1 ([]≽-refl I w1) in
  ⊥-elim (NATneqUNIV (compAllVal I c1 tt))
if-equalInType-NAT u I w t₁ t₂ (EQTBAR x , eqi) w1 e1 =
  let (w2 , e2 , eqi1) = eqi w1 e1 in
  let (w3 , e3 , x1) = x w1 e1 in
  let eqi2 = eqi1 w2 ([]≽-refl I w2) in
  let x2 = x1 w2 (extTrans ([]≽-refl I w2) e2) in
  let (w4 , e4 , z) = if-equalInType-NAT u I w2 t₁ t₂ (x2 , eqi2) w2 ([]≽-refl I w2) in
  (w4 , extTrans e4 (extTrans e2 e3) , z)
if-equalInType-NAT u I w t₁ t₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) = ⊥-elim (NATneqLOWER (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) = ⊥-elim (NATneqSHRINK (compAllVal I x₁ tt))


¬strongMonEq01 : (I : Inh) (w : world) → ¬ strongMonEq I w (NUM 0) (NUM 1)
¬strongMonEq01 I w (n , c₁ , c₂) = eb
  where
    ea : NUM 0 ≡ NUM 1
    ea rewrite compAllVal I c₁ tt | compAllVal I c₂ tt = refl

    eb : ⊥
    eb with ea
    ... | ()


VOID : Term
VOID = EQ (NUM 0) (NUM 1) NAT


weak-consistency : (w : world) → ¬ Σ Term (λ t → eqintype w VOID t t)
weak-consistency w (t , u , n , k , c) = ¬strongMonEq01 I w2 ea5
  where
    ea1 : eqintypeN u n (k + n) w VOID t t
    ea1 = c n ≤-refl

    I : Inh
    I = inhN u n (k + n)

    ea2 : inOpenBar I w (λ w' e' → [ I ] t ⇛ AX at w' × [ I ] t ⇛ AX at w' × equalInType u I w' NAT (NUM 0) (NUM 1))
    ea2 = if-equalInType-EQ u I w NAT (NUM 0) (NUM 1) t t ea1

    w1 : world
    w1 = proj₁ (ea2 w ([]≽-refl I w))

    e1 : [ I ] w1 ⪰ w
    e1 = proj₁ (proj₂ (ea2 w ([]≽-refl I w)))

    ea3 : equalInType u I w1 NAT (NUM 0) (NUM 1)
    ea3 = proj₂ (proj₂ (proj₂ (proj₂ (ea2 w ([]≽-refl I w))) w1 ([]≽-refl I w1)))

    ea4 : inOpenBar I w1 (λ w1 e1 → strongMonEq I w1 (NUM 0) (NUM 1))
    ea4 = if-equalInType-NAT u I w1 (NUM 0) (NUM 1) ea3

    w2 : world
    w2 = proj₁ (ea4 w1 ([]≽-refl I w1))

    e2 : [ I ] w2 ⪰ w1
    e2 = proj₁ (proj₂ (ea4 w1 ([]≽-refl I w1)))

    ea5 : strongMonEq I w2 (NUM 0) (NUM 1)
    ea5 = proj₂ (proj₂ (ea4 w1 ([]≽-refl I w1))) w2 ([]≽-refl I w2)
\end{code}


%Let us now prove further results about this semantics


\begin{code}[hide]
-- ---------------------------------
-- A few useful terms
FUN : Term → Term → Term
FUN a b = PI a b

N0 : Term
N0 = NUM 0

TRUE : Term
TRUE = EQ N0 N0 NAT

SQUASH : Term → Term
SQUASH t = SET TRUE t

NATbinPred : Term
NATbinPred = FUN NAT (FUN NAT (UNIV 0))

BAIRE : Term
BAIRE = FUN NAT NAT

LNAT : Term
LNAT = LOWER NAT

NATlbinPred : Term
NATlbinPred = FUN NAT (FUN LNAT (UNIV 0))

LBAIRE : Term
LBAIRE = FUN NAT LNAT

APPLY2 : Term → Term → Term → Term
APPLY2 a b c = APPLY (APPLY a b) c

LAPPLY : Term → Term → Term
LAPPLY a b = LOWER (APPLY a b)

LAPPLY2 : Term → Term → Term → Term
LAPPLY2 a b c = LOWER (APPLY2 a b c)

acHypPi : (P : Term) → Term
acHypPi P = PI{--2--} NAT (SQUASH{--1--} (SUM{--0--} LNAT (LAPPLY2 P (VAR 2) (VAR 0))))

acConclSum : (P : Term) → Term
acConclSum P = SUM{--1--} LBAIRE (PI{--0--} NAT (LAPPLY2 P (VAR 0) (APPLY (VAR 1) (VAR 0))))

acConclP : (P : Term) → Term
acConclP P = SQUASH{--2--} (acConclSum P)

acHyp : Term
acHyp = acHypPi (VAR 3)

acConcl : Term
acConcl = acConclP (VAR 4)

acFun : Term
acFun = FUN acHyp acConcl


-- AC00
ac : Term
ac = PI NATlbinPred acFun

MEM : Term → Term → Term
MEM a A = EQ a a A

AND : Term → Term → Term
AND a b = SUM a b

FST : Term → Term
FST t = SPREAD t (VAR 1)

SND : Term → Term
SND t = SPREAD t (VAR 0)

acres : (p : Term) → restriction
acres p n t = AND (MEM t NAT) (APPLY2 p (NUM n) t)

dumNotInac : # ac
dumNotInac h ()

closedNum : (n : ℕ) → # (NUM n)
closedNum n h ()

lamAX : Term
lamAX = LAMBDA AX

acext : Term
acext = LAMBDA lamAX



-- ---------------------------------
-- Some simple lemmas
allWimpliesinOpenBar : {I : Inh} {w : world} {f : wPred I w} → allW I w f → inOpenBar I w f
allWimpliesinOpenBar {I} {w} {f} h w1 e1 = (w1 , ([]≽-refl I _ , λ w2 e2 → h w2 ([]≽-trans {I} e2 _)))

eqTypesNAT : (w : world) (I : Inh) (u : univs) → eqTypes u I w NAT NAT
eqTypesNAT w I u =
  EQTNAT (compAllRefl I NAT w) (compAllRefl I NAT w)

strongMonEqN0 : (I : Inh) (w : world) → strongMonEq I w N0 N0
strongMonEqN0 I w =  (0 , (compAllRefl I N0 w , compAllRefl I N0 w))

allInOpenBarStrongMonEqN0 : (I : Inh) (w : world) → allW I w (λ w' e → inOpenBar I w' (λ w'' _ → strongMonEq I w'' N0 N0))
allInOpenBarStrongMonEqN0 I w w1 e1 w2 e2 = (w2 , ([]≽-refl I _ , λ w3 e3 → strongMonEqN0 I w3))

eqTypesTRUE : (w : world) (I : Inh) (u : univs) → eqTypes u I w TRUE TRUE
eqTypesTRUE w I u =
  EQTEQ N0 N0 N0 N0 NAT NAT
        (compAllRefl I (EQ N0 N0 NAT) w)
        (compAllRefl I (EQ N0 N0 NAT) w)
        (λ w1 e1 → eqTypesNAT _ _ _)
        (allInOpenBarStrongMonEqN0 I w)
        (allInOpenBarStrongMonEqN0 I w)



-- wPredExtIrr
wPredExtIrr-equalInType : (u : ℕ) (I1 I2 : Inh) (w : world) (T a b : Term)
                          → wPredExtIrr {I1} {w} (λ w1 e1 → equalInType u I2 w1 T a b)
wPredExtIrr-equalInType u I1 I2 w T a b w' e1 e2 h = h


wPredExtIrr-eqTypes : (u : univs) (I1 I2 : Inh) (w : world) (A B : Term)
                      → wPredExtIrr {I1} {w} (λ w1 e1 → eqTypes u I2 w1 A B)
wPredExtIrr-eqTypes u I1 I2 w A B w' e1 e2 h = h




eqUnivi-mon : (i : ℕ) → mon (eqUnivi i)
eqUnivi-mon i {a} {b} I {w} h w1 e1 =
  inOpenBar-mon I {w1} {w} {λ w' _ → [ I ] a ⇛ (UNIV i) at w' × [ I ] b ⇛ (UNIV i) at w'} (λ w' e2 e3 h → h) e1 h


eqInUnivi-mon : (i : ℕ) → mon (eqInUnivi i)
eqInUnivi-mon (suc i) {a} {b} I {w} (inj₁ x) w1 e1 =
  inj₁ (eqTypes-mon (i , eqUnivi i , eqInUnivi i) (eqUnivi-mon i) I x w1 e1)
eqInUnivi-mon (suc i) {a} {b} I {w} (inj₂ y) w1 e1 =
  inj₂ (eqInUnivi-mon i I y w1 e1)



-- SET
SETinj1 : {a b : Term} {c d : Term} → SET a c ≡ SET b d → a ≡ b
SETinj1 refl =  refl

SETinj2 : {a b : Term} {c d : Term} → SET a c ≡ SET b d → c ≡ d
SETinj2 refl =  refl


-- SET
SETneqNAT : {a : Term} {b : Term} → ¬ (SET a b) ≡ NAT
SETneqNAT {a} {b} ()

SETneqQNAT : {a : Term} {b : Term} → ¬ (SET a b) ≡ QNAT
SETneqQNAT {a} {b} ()

SETneqLT : {a : Term} {b : Term} {c d : Term} → ¬ (SET a b) ≡ LT c d
SETneqLT {a} {b} {c} {d} ()

SETneqQLT : {a : Term} {b : Term} {c d : Term} → ¬ (SET a b) ≡ QLT c d
SETneqQLT {a} {b} {c} {d} ()

SETneqFREE : {a : Term} {b : Term} → ¬ (SET a b) ≡ FREE
SETneqFREE {a} {b} ()

SETneqPI : {a : Term} {b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ PI c d
SETneqPI {a} {b} {c} {d} ()

SETneqSUM : {a : Term} {b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ SUM c d
SETneqSUM {a} {b} {c} {d} ()

SETneqUNION : {a : Term} {b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ UNION c d
SETneqUNION {a} {b} {c} {d} ()

SETneqTSQUASH : {a : Term} {b : Term} {c : Term} → ¬ (SET a b) ≡ TSQUASH c
SETneqTSQUASH {a} {b} {c} ()

SETneqEQ : {a : Term} {b : Term} {c d e : Term} → ¬ (SET a b) ≡ EQ c d e
SETneqEQ {a} {b} {c} {d} {e} ()

SETneqFFDEFS : {a : Term} {b : Term} {c d : Term} → ¬ (SET a b) ≡ FFDEFS c d
SETneqFFDEFS {a} {b} {c} {d} ()

SETneqLOWER : {a : Term} {b : Term} {c : Term} → ¬ (SET a b) ≡ LOWER c
SETneqLOWER {a} {b} {c} ()

SETneqSHRINK : {a : Term} {b : Term} {c : Term} → ¬ (SET a b) ≡ SHRINK c
SETneqSHRINK {a} {b} {c} ()

SETneqUNIV : {a : Term} {b : Term} {n : ℕ} → ¬ (SET a b) ≡ UNIV n
SETneqUNIV {a} {b} {n} ()


-- LOWER
LOWERneqNAT : {a : Term} → ¬ (LOWER a) ≡ NAT
LOWERneqNAT {a} ()

LOWERneqQNAT : {a : Term} → ¬ (LOWER a) ≡ QNAT
LOWERneqQNAT {a} ()

LOWERneqLT : {a : Term} {c d : Term} → ¬ (LOWER a) ≡ LT c d
LOWERneqLT {a} {c} {d} ()

LOWERneqQLT : {a : Term} {c d : Term} → ¬ (LOWER a) ≡ QLT c d
LOWERneqQLT {a} {c} {d} ()

LOWERneqFREE : {a : Term} → ¬ (LOWER a) ≡ FREE
LOWERneqFREE {a} ()

LOWERneqPI : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ PI c d
LOWERneqPI {a} {c} {d} ()

LOWERneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ SUM c d
LOWERneqSUM {a} {c} {d} ()

LOWERneqSET : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ SET c d
LOWERneqSET {a} {c} {d} ()

LOWERneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ UNION c d
LOWERneqUNION {a} {c} {d} ()

LOWERneqTSQUASH : {a : Term} {c : Term} → ¬ (LOWER a) ≡ TSQUASH c
LOWERneqTSQUASH {a} {c} ()

LOWERneqEQ : {a : Term} {c d e : Term} → ¬ (LOWER a) ≡ EQ c d e
LOWERneqEQ {a} {c} {d} {e} ()

LOWERneqFFDEFS : {a : Term} {c d : Term} → ¬ (LOWER a) ≡ FFDEFS c d
LOWERneqFFDEFS {a} {c} {d} ()

LOWERneqUNIV : {a : Term} {n : ℕ} → ¬ (LOWER a) ≡ UNIV n
LOWERneqUNIV {a} {n} ()

LOWERneqSHRINK : {a b : Term} → ¬ LOWER a ≡ SHRINK b
LOWERneqSHRINK {a} {b} ()

LOWERinj : {a b : Term} → LOWER a ≡ LOWER b → a ≡ b
LOWERinj refl =  refl

compAllLOWER : {I : Inh} {w : world} {a b : Term} → [ I ] LOWER a ⇛ LOWER b at w → a ≡ b
compAllLOWER {I} {w} {a} {b} e = LOWERinj (compAllVal I e tt)


-- SHRINK
SHRINKneqNAT : {a : Term} → ¬ (SHRINK a) ≡ NAT
SHRINKneqNAT {a} ()

SHRINKneqQNAT : {a : Term} → ¬ (SHRINK a) ≡ QNAT
SHRINKneqQNAT {a} ()

SHRINKneqLT : {a : Term} {c d : Term} → ¬ (SHRINK a) ≡ LT c d
SHRINKneqLT {a} {c} {d} ()

SHRINKneqQLT : {a : Term} {c d : Term} → ¬ (SHRINK a) ≡ QLT c d
SHRINKneqQLT {a} {c} {d} ()

SHRINKneqFREE : {a : Term} → ¬ (SHRINK a) ≡ FREE
SHRINKneqFREE {a} ()

SHRINKneqPI : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ PI c d
SHRINKneqPI {a} {c} {d} ()

SHRINKneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ SUM c d
SHRINKneqSUM {a} {c} {d} ()

SHRINKneqSET : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ SET c d
SHRINKneqSET {a} {c} {d} ()

SHRINKneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ UNION c d
SHRINKneqUNION {a} {c} {d} ()

SHRINKneqTSQUASH : {a : Term} {c : Term} → ¬ (SHRINK a) ≡ TSQUASH c
SHRINKneqTSQUASH {a} {c} ()

SHRINKneqEQ : {a : Term} {c d e : Term} → ¬ (SHRINK a) ≡ EQ c d e
SHRINKneqEQ {a} {c} {d} {e} ()

SHRINKneqFFDEFS : {a : Term} {c d : Term} → ¬ (SHRINK a) ≡ FFDEFS c d
SHRINKneqFFDEFS {a} {c} {d} ()

SHRINKneqUNIV : {a : Term} {n : ℕ} → ¬ (SHRINK a) ≡ UNIV n
SHRINKneqUNIV {a} {n} ()

SHRINKneqLOWER : {a b : Term} → ¬ SHRINK a ≡ LOWER b
SHRINKneqLOWER {a} {b} ()

SHRINKinj : {a b : Term} → SHRINK a ≡ SHRINK b → a ≡ b
SHRINKinj refl =  refl

compAllSHRINK : {I : Inh} {w : world} {a b : Term} → [ I ] SHRINK a ⇛ SHRINK b at w → a ≡ b
compAllSHRINK {I} {w} {a} {b} e = SHRINKinj (compAllVal I e tt)



closedlamAX : # lamAX
closedlamAX v ()

closedAX : # AX
closedAX v ()

sublamAX : (t : Term) → sub t lamAX ≡ lamAX
sublamAX t = subNotIn t lamAX closedAX

subAX : (t : Term) → sub t AX ≡ AX
subAX t = subNotIn t AX closedAX

closedNAT : # NAT
closedNAT v ()

closedLNAT : # LNAT
closedLNAT v ()

subNAT : (t : Term) → sub t NAT ≡ NAT
subNAT t = subNotIn t NAT closedNAT

subLNAT : (t : Term) → sub t LNAT ≡ LNAT
subLNAT t = subNotIn t LNAT closedLNAT

eqFun : {a b c d : Term} → a ≡ b → c ≡ d → FUN a c ≡ FUN b d
eqFun {a} {b} {c} {d} e f rewrite e rewrite f = refl

closedLe : {u : Term} → # u → (v : Var) → ((w : Var) → v ≤ w → w # u)
closedLe {u} c v w j = c w

subacFun : (t : Term) → # t → sub t acFun ≡ FUN (acHypPi t) (acConclP t)
subacFun t c
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftDownTrivial 3 t (closedLe {t} c 3)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftDownTrivial 4 t (closedLe {t} c 4) = eqFun refl refl

notinnil : {A : Set} (l : List A) → ((v : A) → ¬ (v ∈ l)) → l ≡ []
notinnil {A} [] i = refl
notinnil {A} (x ∷ l) i = ⊥-elim (i x (here refl))

closedfvarsnil : (t : Term) → # t → fvars t ≡ []
closedfvarsnil t c = notinnil (fvars t) c

innilfalse : {A : Set} (v : A) → v ∈ [] → ⊥
innilfalse {A} v ()

closedacConclP : (P : Term) → # P → # (acConclP P)
closedacConclP P c v i
  rewrite lowerVarsApp (fvars P ++ 0 ∷ []) (1 ∷ 0 ∷ [])
  rewrite lowerVarsApp (fvars P) (0 ∷ [])
  rewrite lowerVarsApp (lowerVars (fvars P) ++ []) (0 ∷ [])
  rewrite lowerVarsApp (lowerVars (lowerVars (fvars P) ++ [])) (0 ∷ [])
  rewrite closedfvarsnil P c = innilfalse v i

equalInType-eqTypes : (u : ℕ) (I : Inh) (w : world) (A a b : Term)
                      → equalInType u I w A a b
                      → equalTypes u I w A A
equalInType-eqTypes u I w A a b (eqt , eqi) = eqt

inOpenBarEqualInType-inOpenBarEqTypes : (u : ℕ) (I : Inh) (w : world) (A a b : Term)
                                        → inOpenBar I w (λ w' _ → equalInType u I w' A a b)
                                        → inOpenBar I w (λ w' _ → equalTypes u I w' A A)
inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h w1 e1 =
  let (w2 , (e2 , eqt2)) = h w1 e1 in
  (w2 , (e2 , λ w3 e3 → fst (eqt2 w3 e3)))

inOpenBarStrongMonEqNUM : (I : Inh) (w : world) (n : ℕ)
                          → inOpenBar I w (λ w1 e1 → strongMonEq I w1 (NUM n) (NUM n))
inOpenBarStrongMonEqNUM I w n w1 e1 =
  (w1 , ([]≽-refl I w1 , λ w2 e2 → (n , (compAllRefl I (NUM n) w2 , compAllRefl I (NUM n) w2))))

equalInTypeNAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT u I w t₁ t₂ e = (eqTypesNAT w I (uni u) , e)

equalInTypeNAT2 : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → strongMonEq I w t₁ t₂
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT2 u I w t₁ t₂ e =
  equalInTypeNAT u I w t₁ t₂
    λ w1 e1 → (w1 , []≽-refl I w1 , λ w2 e2 → strongMonEq-mon I e w2 ([]≽-trans {I} e2 e1))

numInNAT : (u : ℕ) (I : Inh) (w : world) (n : ℕ)
           → equalInType u I w NAT (NUM n) (NUM n)
numInNAT u I w n = equalInTypeNAT u I w (NUM n) (NUM n) (inOpenBarStrongMonEqNUM I w n)


inOpenBarMP : (I : Inh) (w : world) (f g : wPred I w)
              → allW I w (λ w1 e1 → f w1 e1 → g w1 e1)
              → inOpenBar I w f → inOpenBar I w g
inOpenBarMP I w f g i j w1 e1 =
  let (w2 , (e2 , h)) = j w1 e1 in
  (w2 , (e2 , λ w3 e3 → let z = h w3 e3 in i w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2 e1)) z))

inOpenBarIdem : (I : Inh) (w : world) (f : wPred I w) (c : wPredExtIrr {I} {w} f)
                → inOpenBar I w (λ w1 e1 → inOpenBar I w1 (↑wPred I f e1))
                → inOpenBar I w f
inOpenBarIdem I w f c i w1 e1 =
  let (w2 , (e2 , i1)) = i w1 e1 in
  let (w3 , (e3 , i2)) = i1 _ ([]≽-refl I _) _ ([]≽-refl I _) in
  (w3 , ([]≽-trans {I} e3 e2 , λ w4 e4 → let i3 = i2 w4 e4 in c w4 _ _ i3))


substEqTeq : (u : univs) (I1 I2 : Inh) (w : world) (A1 A2 B1 B2 a₁ a₂ : Term)
             (eqt : eqTypes u I1 w A1 B1) (eqi : eqInType u I1 w eqt a₁ a₂)
             → I1 ≡ I2
             → A1 ≡ A2
             → B1 ≡ B2
             → Σ (eqTypes u I2 w A2 B2) (λ eqt → eqInType u I2 w eqt a₁ a₂)
substEqTeq u I1 I2 w A1 A2 B1 B2 a₁ a₂ eqt eqi e1 e2 e3 rewrite e1 | e2 | e3 = (eqt , eqi)

strongMonEqsym : (I : Inh) {w : world} {a b : Term} → strongMonEq I w a b → strongMonEq I w b a
strongMonEqsym I {w} {a} {b} (n , c1 , c2) = (n , c2 , c1)

inOpenBarstrongMonEqsym : (I : Inh) {w : world} {a b : Term}
                          → inOpenBar I w (λ w' _ → strongMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → strongMonEq I w' b a)
inOpenBarstrongMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , e2 , z) = h w1 e1 in
  (w2 , e2 , λ w3 e3 → strongMonEqsym I (z w3 e3))

weakMonEqsym : (I : Inh) {w : world} {a b : Term} → weakMonEq I w a b → weakMonEq I w b a
weakMonEqsym I {w} {a} {b} m w1 e1 = let (n , c1 , c2) = m _ e1 in (n , c2 , c1)

inOpenBarweakMonEqsym : (I : Inh) {w : world} {a b : Term}
                          → inOpenBar I w (λ w' _ → weakMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → weakMonEq I w' b a)
inOpenBarweakMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , e2 , z) = h _ e1 in
   (_ , e2 , λ w3 e3 → weakMonEqsym I (z _ e3))

eqSQUASH : {a b : Term} → a ≡ b → SQUASH a ≡ SQUASH b
eqSQUASH {a} {b} e rewrite e = refl

eqAPPLY : {a b c d : Term} → a ≡ b → c ≡ d → APPLY a c ≡ APPLY b d
eqAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl

eqLAPPLY : {a b c d : Term} → a ≡ b → c ≡ d → LAPPLY a c ≡ LAPPLY b d
eqLAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl

sub-NUM-SQUASH-SUM : (n : ℕ) (p : Term) → # p →
                     sub (NUM n) (SQUASH (SUM LNAT (LAPPLY2 p (VAR 2) (VAR 0))))
                     ≡ SQUASH (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0)))
sub-NUM-SQUASH-SUM n p cp rewrite subvNotIn 2 (NUM n) p (cp _)
                                | shiftDownTrivial 2 p (λ w c → cp _) = eqSQUASH refl


sub-LAPPLY2-NUM-VAR : (t p : Term) (n : ℕ) → # p → sub t (LAPPLY2 p (NUM n) (VAR 0)) ≡ LAPPLY2 p (NUM n) t
sub-LAPPLY2-NUM-VAR t p n cp rewrite subvNotIn 0 (shiftUp 0 t) p (cp _)
                                   | shiftDownTrivial 0 p (λ w c → cp _)
                                   | shiftDownUp t 0 = eqLAPPLY refl refl

equalInTypesubLAPPLY2 : {u : ℕ} {I : Inh} {w : world} {p t a b : Term} {n : ℕ}
                       → # p
                       → equalInType u I w (sub t (LAPPLY2 p (NUM n) (VAR 0))) a b
                       → equalInType u I w (LAPPLY2 p (NUM n) t) a b
equalInTypesubLAPPLY2 {u} {I} {w} {p} {t} {a} {b} {n} cp e rewrite sub-LAPPLY2-NUM-VAR t p n cp = e

#APPLY2-NUM : (p m : Term) (n : ℕ) → # p → # m → # APPLY2 p (NUM n) m
#APPLY2-NUM p m n cp cm v i rewrite ++[] (fvars p) with ∈-++⁻ (fvars p) i
... | inj₁ x = cp _ x
... | inj₂ x = cm _ x


wPredExtIrrFun-allI-equalInType : (u : ℕ) (I1 I2 : Inh) (w : world) (T a b : Term)
                                  → wPredExtIrr {I1} {w} (λ w1 e1 → allI I2 (λ i → equalInType u i w1 T a b))
wPredExtIrrFun-allI-equalInType u I1 I2 w T a b w' e1 e2 h = h



-- LOWER properties
eqTypesLOWER : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term) (wf : wfInh< I)
               → inOpenBar I w (λ w' _ → allI (lower I) (λ i → equalInType u i w' T a₁ a₂))
               → eqTypes (uni u) I w (LOWER T) (LOWER T)
eqTypesLOWER u I w T a₁ a₂ wf h = EQTBAR e
  where
    e : inOpenBar I w (λ w' _ → eqTypes (uni u) I w' (LOWER T) (LOWER T))
    e = λ w1 e1 → let (w2 , e2 , a2) = h w1 e1 in
          (w2 , e2 , λ w3 e3 →
          EQTLOWER T T (compAllRefl I (LOWER T) w3) (compAllRefl I (LOWER T) w3)
            λ w4 e4 → let a3 = a2 w4 ([]≽-trans {I} e4 e3) in
            λ j c₁ c₂ k c₃ c₄ → let (eqt , eqi) = a3 j c₁ c₂ k c₃ c₄ in eqt)


impliesEqualInTypeLower : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                          → allW I w (λ w' _ → allI (lower I) (λ i → equalInType u i w' T a₁ a₂))
                          → equalInType u I w (LOWER T) a₁ a₂
impliesEqualInTypeLower u I w T a₁ a₂ e =
  let e' : allW I w (λ w' _ → allI (lower I) (λ i → eqTypes (uni u) i w' T T))
      e' = (λ w1 e1 i c₁ c₂ k c₃ c₄ → let (eqt , eqi) = e w1 e1 i c₁ c₂ k c₃ c₄ in eqt) in
   (EQTLOWER T T (compAllRefl I (LOWER T) w) (compAllRefl I (LOWER T) w) e' ,
    allWimpliesinOpenBar {I} {w} λ w1 e1 i c₁ c₂ k c₃ c₄ → proj₂ (e w1 e1 i c₁ c₂ k c₃ c₄))


equalInTypeLower : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                   → equalInType u I w (LOWER T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → allI (lower I) (λ i → equalInType u i w1 T a₁ a₂))
equalInTypeLower u I w T a₁ a₂ (EQTNAT x x₁ , eqi) = ⊥-elim (LOWERneqNAT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (LOWERneqQNAT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LOWERneqLT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LOWERneqQLT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTFREE x x₁ , eqi) = ⊥-elim (LOWERneqFREE (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (LOWERneqPI (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (LOWERneqSUM (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (LOWERneqSET (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) = ⊥-elim (LOWERneqEQ (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (LOWERneqUNION (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (LOWERneqTSQUASH (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (LOWERneqFFDEFS (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , e) = x w ([]≽-refl I w) in
  let (c1 , c2) = e w1 ([]≽-refl I w1) in
  let c = compAllVal I c1 tt in
  ⊥-elim (LOWERneqUNIV c)
equalInTypeLower u I w T a₁ a₂ (EQTBAR x , eqi) =
  inOpenBarIdem
    I w _ (wPredExtIrrFun-allI-equalInType u I (lower I) w T a₁ a₂)
    λ w1 e1 →
     let (w2' , e2' , eqi1) = eqi w1 e1 in
     let (w2 , e2 , x1) = x w1 e1 in
      (w2' , ([]≽-trans {I} e2' e2 , λ w3 e3 →
        let x2 = x1 w3 ([]≽-trans {I} e3 e2') in
        let eqi2 = eqi1 w3 e3 in
        equalInTypeLower u I w3 T a₁ a₂ (x2 , eqi2) ))
equalInTypeLower u I w T a₁ a₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) =
  λ w1 e1 →
    let (w2' , e2' , eqi1) = eqi w1 e1 in
    (w2' , e2' , λ w3 e3 i c₁ c₂ k c₃ c₄ →
      let eqi2 = eqi1 w3 e3 i c₁ c₂ k c₃ c₄ in
      let eqt2 = eqt w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2' e1)) i c₁ c₂ k c₃ c₄ in
      let eq1 = compAllLOWER {I} x in
      let eq2 = compAllLOWER {I} x₁ in
      substEqTeq (uni u) _ _ w3 A1 T A2 T a₁ a₂ eqt2 eqi2 refl (sym eq1) (sym eq2))
equalInTypeLower u I w T a₁ a₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) = ⊥-elim (LOWERneqSHRINK (compAllVal I x₁ tt))


-- SHRINK properties
eqTypesSHRINK : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term) (wf : wfInh< I)
               → inOpenBar I w (λ w' _ → allI (shrink I) (λ i → equalInType u i w' T a₁ a₂))
               → eqTypes (uni u) I w (SHRINK T) (SHRINK T)
eqTypesSHRINK u I w T a₁ a₂ wf h = EQTBAR e
  where
    e : inOpenBar I w (λ w' _ → eqTypes (uni u) I w' (SHRINK T) (SHRINK T))
    e = λ w1 e1 → let (w2 , e2 , a2) = h w1 e1 in
          (w2 , e2 , λ w3 e3 →
          EQTSHRINK T T (compAllRefl I (SHRINK T) w3) (compAllRefl I (SHRINK T) w3)
            λ w4 e4 → let a3 = a2 w4 ([]≽-trans {I} e4 e3) in
            λ j c₁ c₂ k c₃ c₄ → let (eqt , eqi) = a3 j c₁ c₂ k c₃ c₄ in eqt)

impliesEqualInTypeShrink : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                          → allW I w (λ w' _ → allI (shrink I) (λ i → equalInType u i w' T a₁ a₂))
                          → equalInType u I w (SHRINK T) a₁ a₂
impliesEqualInTypeShrink u I w T a₁ a₂ e =
  let e' : allW I w (λ w' _ → allI (shrink I) (λ i → eqTypes (uni u) i w' T T))
      e' = (λ w1 e1 i c₁ c₂ k c₃ c₄ → let (eqt , eqi) = e w1 e1 i c₁ c₂ k c₃ c₄ in eqt) in
   (EQTSHRINK T T (compAllRefl I (SHRINK T) w) (compAllRefl I (SHRINK T) w) e' ,
    allWimpliesinOpenBar {I} {w} λ w1 e1 i c₁ c₂ k c₃ c₄ → proj₂ (e w1 e1 i c₁ c₂ k c₃ c₄))

equalInTypeShrink : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                   → equalInType u I w (SHRINK T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → allI (shrink I) (λ i → equalInType u i w1 T a₁ a₂))
equalInTypeShrink u I w T a₁ a₂ (EQTNAT x x₁ , eqi) = ⊥-elim (SHRINKneqNAT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (SHRINKneqQNAT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SHRINKneqLT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SHRINKneqQLT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTFREE x x₁ , eqi) = ⊥-elim (SHRINKneqFREE (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (SHRINKneqPI (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (SHRINKneqSUM (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (SHRINKneqSET (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) = ⊥-elim (SHRINKneqEQ (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (SHRINKneqUNION (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (SHRINKneqTSQUASH (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (SHRINKneqFFDEFS (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , e) = x w ([]≽-refl I w) in
  let (c1 , c2) = e w1 ([]≽-refl I w1) in
  let c = compAllVal I c1 tt in
  ⊥-elim (SHRINKneqUNIV c)
equalInTypeShrink u I w T a₁ a₂ (EQTBAR x , eqi) =
  inOpenBarIdem
    I w _ (wPredExtIrrFun-allI-equalInType u I (shrink I) w T a₁ a₂)
    λ w1 e1 →
     let (w2' , e2' , eqi1) = eqi w1 e1 in
     let (w2 , e2 , x1) = x w1 e1 in
      (w2' , ([]≽-trans {I} e2' e2 , λ w3 e3 →
        let x2 = x1 w3 ([]≽-trans {I} e3 e2') in
        let eqi2 = eqi1 w3 e3 in
        equalInTypeShrink u I w3 T a₁ a₂ (x2 , eqi2) ))
equalInTypeShrink u I w T a₁ a₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) = ⊥-elim (SHRINKneqLOWER (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) =
  λ w1 e1 →
    let (w2' , e2' , eqi1) = eqi w1 e1 in
    (w2' , e2' , λ w3 e3 i c₁ c₂ k c₃ c₄ →
      let eqi2 = eqi1 w3 e3 i c₁ c₂ k c₃ c₄ in
      let eqt2 = eqt w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2' e1)) i c₁ c₂ k c₃ c₄ in
      let eq1 = compAllSHRINK {I} x in
      let eq2 = compAllSHRINK {I} x₁ in
      substEqTeq (uni u) _ _ w3 A1 T A2 T a₁ a₂ eqt2 eqi2 refl (sym eq1) (sym eq2))


-- Inhabitation properties
Inh-eta : (I : Inh) → mkinh (Inh.m I) (Inh.n I) (λ m i c → Inh.f I m i (≤-trans c ≤-refl)) ≡ I
Inh-eta (mkinh m n f) = eq-mkinh (fext (λ m → fext (λ i → fext (λ c → eqf m i c))))
  where
    eqf : (m : ℕ) (i : ℕ) (c : i ≤ n) → f m i (≤-trans c ≤-refl) ≡ f m i c
    eqf m i c rewrite ≤-trans-≤-refl c = refl


allI-equalInType : (u : ℕ) (I : Inh) (wf : wfInh≤ I) (w : world) (T a b : Term)
                   → allI I (λ i → equalInType u i w T a b)
                   → equalInType u I w T a b
allI-equalInType u I wf w T a b h =
  subst
    (λ x → equalInType u x w T a b)
    (Inh-eta I)
    (h (Inh.n I) wf ≤-refl (Inh.m I) ≤-refl wf)


s≤-≤pred : {i j : ℕ} → suc j ≤ i → j ≤ pred i
s≤-≤pred {suc i} {j} (_≤_.s≤s h) = h


≤0-≡0 : {j : ℕ} → j ≤ 0 → j ≡ 0
≤0-≡0 {.0} _≤_.z≤n = refl


pred≤pred : {i j : ℕ} → j ≤ i → pred j ≤ pred i
pred≤pred {i} {0} h = _≤_.z≤n
pred≤pred {suc i} {suc j} (_≤_.s≤s h) = h


between2 : {i j : ℕ} (c₁ : j ≤ i) (c₂ : i ≤ suc j) → i ≡ j ⊎ i ≡ (suc j)
between2 {.0} {j} c₁ _≤_.z≤n = inj₁ (sym (≤0-≡0 c₁))
between2 {suc k} {0} c₁ (_≤_.s≤s c₂) rewrite (≤0-≡0 c₂) = inj₂ refl
between2 {suc k} {suc j} c₁ (_≤_.s≤s c₂) with between2 (sucLeInj c₁) c₂
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p rewrite p = inj₂ refl


between1 : {i j : ℕ} (c₁ : j ≤ i) (c₂ : i ≤ j) → i ≡ j
between1 {0} {j} c₁ _≤_.z≤n rewrite (≤0-≡0 c₁) = refl
between1 {suc k} {suc w} c₁ (_≤_.s≤s c₂) rewrite between1 (sucLeInj c₁) c₂ = refl


inhL-pred : (u i j m i0 : ℕ) (c : i0 ≤ pred i) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
            → inhL u m (pred i) i0 c w T ≡ Inh.f (inhN2L u j) m i0 (≤-trans c (pred≤pred c₂)) w T
inhL-pred u i j m i0 c c₁ c₂ w T with between2 c₁ c₂ | m≤n⇒m<n∨m≡n (≤-trans c (pred≤pred c₂))
... | inj₁ p | inj₁ q rewrite p | ≤-irrelevant (sucLeInj q) c = refl
... | inj₁ p | inj₂ q rewrite p | q = ⊥-elim (¬s≤ _ c)
... | inj₂ p | inj₁ q rewrite p with m≤n⇒m<n∨m≡n c
...                                | inj₁ r rewrite ≤-irrelevant (sucLeInj r) (sucLeInj q) = refl
...                                | inj₂ r rewrite r = ⊥-elim (¬s≤ _ q)
inhL-pred u i j m i0 c c₁ c₂ w T | inj₂ p | inj₂ q rewrite p | q with m≤n⇒m<n∨m≡n c
... | inj₁ r = ⊥-elim (¬s≤ _ r)
... | inj₂ r = refl


inhm-inhN2Ls : (u j : ℕ) → Inh.m (inhN2Ls u j) ≡ suc j
inhm-inhN2Ls u j = refl


inh-f-inhN2Ls : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
                → Σ Term (λ t → equalInType u (inhN u (suc j) (pred i)) w T t t)
                → Inh.f (inhN2Ls u j) (Inh.m (inhN2Ls u j)) i c₂ w T
inh-f-inhN2Ls u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls u j i c₁ c₂ w T h | inj₂ p rewrite p = h


inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
                     (k : ℕ) (c₃ : j ≤ k) (c₄ : k ≤ pred i)
                     (w : world) (T : Term)
                     → Σ Term (λ t → equalInType u (inhN u k (pred i)) w T t t)
                     → Inh.f (inhN2Ls u j) k i c₂ w T
inh-f-inhN2Ls-pred u j i c₁ c₂ k c₃ c₄ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls-pred u j i c₁ c₂ k c₃ c₄ w T h | inj₂ p rewrite p = h


if-inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
                        → Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) i c₂ w T
                        → Σ Term (λ t → equalInType u (inhN u j (pred i)) w T t t)
if-inh-f-inhN2Ls-pred u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls-pred u j i c₁ c₂ w T h | inj₂ p rewrite p = h


allI-inhN2Ls-ΣequalInType : (u j i : ℕ) (w : world) (t : Term) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
                            → allIW (inhN2Ls u j) (λ i → i w t)
                            → Σ Term (λ z → equalInType u (inhN u j i) w t z z)
allI-inhN2Ls-ΣequalInType u j i w t c₁ c₂ h =
  if-inh-f-inhN2Ls-pred
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) j ≤-refl c₁)


if-inh-f-inhN2Ls-pred2 : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
                         (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
                         (w : world) (T : Term)
                         → Inh.f (inhN2Ls u j) k i c₂ w T
                         → Σ Term (λ t → equalInType u (inhN u k (pred i)) w T t t)
if-inh-f-inhN2Ls-pred2 u j i c₁ c₂ k c₃ c₄ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls-pred2 u j i c₁ c₂ k c₃ c₄ w T h | inj₂ p rewrite p = h


allI-inhN2Ls-ΣequalInType2 : (u j i : ℕ) (w : world) (t : Term) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
                             (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
                            → allIW (inhN2Ls u j) (λ i → i w t)
                            → Σ Term (λ z → equalInType u (inhN u k i) w t z z)
allI-inhN2Ls-ΣequalInType2 u j i w t c₁ c₂ k c₃ c₄ h =
  if-inh-f-inhN2Ls-pred2
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) k c₃ (≤-trans c₄ (n≤1+n _)) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) k (≤-trans (n≤1+n _) c₃) c₄)


mkinh2L≡inhNaux : (u j i : ℕ) (c₁ : j ≤ i) (c₂ : i ≤ suc j) (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
                → Inh.f (inhN2L u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
mkinh2L≡inhNaux u j i c₁ c₂ m z c w t with between2 c₁ c₂ | m≤n⇒m<n∨m≡n (≤-trans c c₂)
... | inj₁ p | inj₁ q rewrite p | ≤-irrelevant (sucLeInj q) c = refl
... | inj₁ p | inj₂ q rewrite p | q = ⊥-elim (¬s≤ _ c)
... | inj₂ p | inj₁ q rewrite p with m≤n⇒m<n∨m≡n c
...                                | inj₁ r rewrite ≤-irrelevant (sucLeInj r) (sucLeInj q) = refl
...                                | inj₂ r rewrite r = ⊥-elim (¬s≤ _ q)
mkinh2L≡inhNaux u j i c₁ c₂ m z c w t | inj₂ p | inj₂ q rewrite p | q with m≤n⇒m<n∨m≡n c
... | inj₁ r = ⊥-elim (¬s≤ _ r)
... | inj₂ r = refl


mkinh2L≡inhN : (u j i : ℕ) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
               → mkinh (Inh.m (inhN2L u j)) i (λ m i c → Inh.f (inhN2L u j) m i (≤-trans c c₂)) ≡ inhN u j i
mkinh2L≡inhN u j i c₁ c₂ = eq-mkinh (fext (λ m → fext (λ z → fext (λ c → fext (λ w → fext (λ t → h m z c w t))))))
  where
    h : (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
        → Inh.f (inhN2L u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
    h m z c w t = mkinh2L≡inhNaux u j i c₁ c₂ m z c w t


mkinh1Ls≡inhNaux : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j) (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
                 → Inh.f (inhN1Ls u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
mkinh1Ls≡inhNaux u j i c₁ c₂ m z c w t with between1 c₁ c₂
... | p rewrite p with m≤n⇒m<n∨m≡n (≤-trans c c₂) | m≤n⇒m<n∨m≡n c
...               | inj₁ x | inj₁ y rewrite ≤-irrelevant (sucLeInj x) (sucLeInj y) = refl
...               | inj₁ x | inj₂ y rewrite y = ⊥-elim (¬s≤ _ x)
...               | inj₂ x | inj₁ y rewrite x = ⊥-elim (¬s≤ _ y)
...               | inj₂ x | inj₂ y rewrite x | y = refl


mkinh1Ls≡inhN : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j) (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
              → mkinh k i (λ m i c → Inh.f (inhN1Ls u j) m i (≤-trans c c₂)) ≡ inhN u k i
mkinh1Ls≡inhN u j i c₁ c₂ k c₃ c₄ = eq-mkinh (fext (λ m → fext (λ z → fext (λ c → fext (λ w → fext (λ t → h m z c w t))))))
  where
    h : (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
        → Inh.f (inhN1Ls u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
    h m z c w t = mkinh1Ls≡inhNaux u j i c₁ c₂ m z c w t


{--
if-inh-f-inhN2Ls : (u j : ℕ) (w : world) (T : Term)
                   → Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) (suc (suc j)) ≤-refl w T
                   → Σ Term (λ t → equalInType u (inhN u (suc j) (suc j)) w T t t)
if-inh-f-inhN2Ls u j w T h with m≤n⇒m<n∨m≡n (≤-refl {suc (suc j)})
... | inj₁ p = ⊥-elim (¬s≤ _ p)
... | inj₂ p = {!h!}

{-- with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ q)
...          | inj₂ q = {!h!}
if-inh-f-inhN2Ls u j w T h | inj₂ p = {!!} --}

{-- with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls u j i c₁ c₂ w T h | inj₂ p rewrite p = h --}


allI-inhN2Ls-ΣequalInType1Ls : (u j i : ℕ) (w : world) (t : Term) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j)
                               → allIW (inhN2Ls u j) (λ i → i w t)
                               → Σ Term (λ z → equalInType u (inhN u (suc j) i) w t z z)
allI-inhN2Ls-ΣequalInType1Ls u j i w t c₁ c₂ h = se2
  where
    se0 : Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) (suc (suc j)) ≤-refl w t
    se0 = h (suc (suc j)) (n≤1+n _) ≤-refl

    se1 : Σ Term (λ z → equalInType u (inhN u (suc j) (suc j)) w t z z)
    se1 = {!!}

    se2 : Σ Term (λ z → equalInType u (inhN u (suc j) i) w t z z)
    se2 rewrite between1 c₁ c₂ = se1
--}


--with between1 c₁ c₂
--... | p rewrite p = {!!}
{--  if-inh-f-inhN2Ls-pred
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂)) --}


inhN≡inhN1Ls : {u j i k : ℕ} → suc j ≤ i → i ≤ suc j → suc j ≤ k → k ≤ i
               → inhN u k i ≡ inhN1Ls u j
inhN≡inhN1Ls {u} {j} {i} {k} a b c d rewrite between1 a b | between1 c d = refl


allI-inhN2Ls-allI-inh1Ls : {u j : ℕ} {f : InhW → Set}
                           → allIW (inhN2Ls u j) f
                           → allIW (inhN1Ls u j) f
allI-inhN2Ls-allI-inh1Ls {u} {j} {f} h i ci₁ ci₂ k ck₁ ck₂ =
  let z = h i ci₁ (≤-trans ci₂ (n≤1+n _)) k ck₁ ck₂ in
  subst f (sym e1) z
  where
    e2 : (w : world) (T : Term) → Inh.f (inhN1Ls u j) k i ci₂ w T ≡ Inh.f (inhN2Ls u j) k i (≤-trans ci₂ (n≤1+n (Inh.n (inhN1Ls u j)))) w T
    e2 w T with between1 ci₁ ci₂
    ... | p rewrite p with m≤n⇒m<n∨m≡n ci₂
    ...               | inj₁ q = ⊥-elim (¬s≤ _ q)
    ...               | inj₂ q with m≤n⇒m<n∨m≡n (≤-trans ci₂ (_≤_.s≤s (≤-step (≤-reflexive refl))))
    ...                        | inj₂ r = ⊥-elim (¬≡s _ r)
    ...                        | inj₁ r with m≤n⇒m<n∨m≡n (sucLeInj r)
    ...                                 | inj₁ s = ⊥-elim (¬s≤ _ s)
    ...                                 | inj₂ s = refl

    e1 : Inh.f (inhN1Ls u j) k i ci₂ ≡ Inh.f (inhN2Ls u j) k i (≤-trans ci₂ (n≤1+n (Inh.n (inhN1Ls u j))))
    e1 = fext (λ w → fext (λ T → e2 w T))


[]≽-inhN2Ls-[]≽-inhN1Ls : {w2 w1 : world} {u j : ℕ}
                     → [ inhN2Ls u j ] w2 ⪰ w1
                     → [ inhN1Ls u j ] w2 ⪰ w1
[]≽-inhN2Ls-[]≽-inhN1Ls {w2} {.w2} {u} {j} (extRefl .w2) = extRefl w2
[]≽-inhN2Ls-[]≽-inhN1Ls {w2} {w1} {u} {j} (extTrans h h₁) = extTrans ([]≽-inhN2Ls-[]≽-inhN1Ls h) ([]≽-inhN2Ls-[]≽-inhN1Ls h₁)
[]≽-inhN2Ls-[]≽-inhN1Ls {.(w1 ++ choice name t ∷ [])} {w1} {u} {j} (extChoice .w1 name l t res x x₁) =
  extChoice w1 name l t res x (allI-inhN2Ls-allI-inh1Ls {u} {j} {λ i → i w1 (res (length l) t)} x₁)
[]≽-inhN2Ls-[]≽-inhN1Ls {.(w1 ++ start name res ∷ [])} {w1} {u} {j} (extEntry .w1 name res x) =
  extEntry w1 name res x


[]≽-inhN2Ls-to-N1s : {w2 w1 : world} {u j i k : ℕ} → suc j ≤ i → i ≤ suc j → suc j ≤ k → k ≤ i
                     → [ inhN2Ls u j ] w2 ⪰ w1
                     → [ inhN u k i ] w2 ⪰ w1
[]≽-inhN2Ls-to-N1s {w2} {w1} {u} {j} {i} {k} a b c d h rewrite inhN≡inhN1Ls {u} {j} {i} {k} a b c d =
  []≽-inhN2Ls-[]≽-inhN1Ls h


{--then-lower : (w : world) (a b : Term) → eqintype w NAT a b → eqintype w (LOWER NAT) a b
then-lower w a b (u , n , k , e) =
  (u , suc n , k , λ j c →
   impliesEqualInTypeLower u (inhN u j (k + j)) w NAT a b λ w1 e1 → {!!})

if-lower : (w : world) (a b : Term) → eqintype w (LOWER NAT) a b → eqintype w NAT a b
if-lower w a b (u , n , k , e) = (u , n , k , λ j c → {!!})--}
--}

\end{code}
