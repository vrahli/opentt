\begin{code}

--open import bar
--module props1 (bar : Bar) where

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
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import world
open import choice


--module props1 (bar : Bar) where
module props1 (W : PossibleWorlds) (C : Choice W) (E : Extensionality 0ℓ 2ℓ) where


open import worldDef(W)
open import computation(W)(C)
open import bar(W)
open import theory(W)(C)(E)
open import props0(W)(C)(E)
open import ind2(W)(C)(E)
open import terms(W)(C)(E)

open import type_sys_props_nat(W)(C)(E)
open import type_sys_props_qnat(W)(C)(E)
open import type_sys_props_lt(W)(C)(E)
open import type_sys_props_qlt(W)(C)(E)
open import type_sys_props_free(W)(C)(E)
open import type_sys_props_pi(W)(C)(E)
open import type_sys_props_sum(W)(C)(E)
open import type_sys_props_set(W)(C)(E)
open import type_sys_props_eq(W)(C)(E)
open import type_sys_props_union(W)(C)(E)
open import type_sys_props_tsquash(W)(C)(E)
open import type_sys_props_ffdefs(W)(C)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar) -- this is the one where a function is not recognized as terminating, but does not break the bar abstraction
\end{code}




\begin{code}[hide]
UNIVinj : {a b : ℕ} → UNIV a ≡ UNIV b → a ≡ b
UNIVinj refl =  refl


UNIVneqNAT : {a : ℕ} → ¬ UNIV a ≡ NAT
UNIVneqNAT {a} ()

UNIVneqQNAT : {a : ℕ} → ¬ UNIV a ≡ QNAT
UNIVneqQNAT {a} ()

UNIVneqLT : {a : ℕ} {c d : Term} → ¬ UNIV a ≡ LT c d
UNIVneqLT {a} {c} {d} ()

UNIVneqQLT : {a : ℕ} {c d : Term} → ¬ UNIV a ≡ QLT c d
UNIVneqQLT {a} {c} {d} ()

UNIVneqFREE : {a : ℕ} → ¬ UNIV a ≡ FREE
UNIVneqFREE {a} ()

UNIVneqPI : {a : ℕ} {c : Term} {d : Term} → ¬ UNIV a ≡ PI c d
UNIVneqPI {a} {c} {d} ()

UNIVneqSUM : {a : ℕ} {c : Term} {d : Term} → ¬ UNIV a ≡ SUM c d
UNIVneqSUM {a} {c} {d} ()

UNIVneqSET : {a : ℕ} {c : Term} {d : Term} → ¬ UNIV a ≡ SET c d
UNIVneqSET {a} {c} {d} ()

UNIVneqUNION : {a : ℕ} {c : Term} {d : Term} → ¬ UNIV a ≡ UNION c d
UNIVneqUNION {a} {c} {d} ()

UNIVneqEQ : {a : ℕ} {c d e : Term} → ¬ UNIV a ≡ EQ c d e
UNIVneqEQ {a} {c} {d} {e} ()

UNIVneqFFDEFS : {a : ℕ} {c d : Term} → ¬ UNIV a ≡ FFDEFS c d
UNIVneqFFDEFS {a} {c} {d} ()

UNIVneqTSQUASH : {a : ℕ} {c : Term} → ¬ UNIV a ≡ TSQUASH c
UNIVneqTSQUASH {a} {c} ()

UNIVneqLIFT : {a : ℕ} {c : Term} → ¬ UNIV a ≡ LIFT c
UNIVneqLIFT {a} {c} ()

UNIVneqDUM : {a : ℕ} {c : Term} → ¬ UNIV a ≡ DUM c
UNIVneqDUM {a} {c} ()

UNIVneqLOWER : {a : ℕ} {c : Term} → ¬ UNIV a ≡ LOWER c
UNIVneqLOWER {a} {c} ()

UNIVneqSHRINK : {a : ℕ} {c : Term} → ¬ UNIV a ≡ SHRINK c
UNIVneqSHRINK {a} {c} ()


is-TSP-univs : (u : univs) → Set₁
is-TSP-univs u = (w : 𝕎·) (A B : CTerm) (p : eqTypes u w A B) → TSP {u} {w} {A} {B} p


{--mon-univs : (u : univs) → Set₁
mon-univs u = {!!} --mon (fst (snd u))--}


typeSysConds-BAR-ttrans : (u : univs) (w : 𝕎·) (A B C : CTerm)
                          (x : inbar w (λ w' _ → eqTypes u w' A B))
                          → inbar' w x (λ w1 e1 → TSP)
                          → eqTypes u w B C
                          → eqTypes u w A C
typeSysConds-BAR-ttrans u w A B C x i eqt = EQTBAR (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar x aw i)
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ : eqTypes u w' A B) (at : atbar x w' e' x₁) → TSP x₁ → eqTypes u w' A C)
    aw w1 e1 eqta at tsp = TSP.ttrans tsp C (eqTypes-mon u eqt w1 e1)




{--
eqInType-⇛-PI2 : (u : univs) (isu : is-universe u) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  → (c₁ : A ⇛ PI A1 B1 at w) (c₂ : B ⇛ PI A2 B2 at w)
                  → eqInTypeExt (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb)
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
{-# TERMINATING #-}
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTNAT x x₁) ei = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTQNAT x x₁) ei = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTFREE x x₁) ei = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei
  = {!!} {--rewrite PIinj1 (⇛-val-det tt tt c₁ x)
        | PIinj2 (⇛-val-det tt tt c₁ x)
        | PIinj1 (⇛-val-det tt tt c₂ x₁)
        | PIinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.∀𝕎-inBarFunc inOpenBar-Bar aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b
                         → PIeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = snd (indb w1 e1 a₁ a₂ eqa (eqtb₁ w1 e1 a₁ a₂ eqa') (APPLY a a₁) (APPLY b a₂)) eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a₁ a₂
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a₁ a₂ eqa') (APPLY a a₁) (APPLY b a₂)
        eqb' = z a₁ a₂ eqa'--}

eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB) ei = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-PI2 u isu w A B A1 A2 B1 B2 a b eqta eqtb c₁ c₂ ext (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar aw x ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → PIeq (eqInType u w'' (eqta w'' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa)) a b))
    aw0 w1 e1 z ez =
      eqInType-⇛-PI2
        u isu w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) {!!} z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → PIeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) a b))
    aw w1 e1 z ez = {!!} --Bar.∀𝕎-inBarFunc inOpenBar-Bar (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb inda indb a b w1 e1) (aw0 w1 e1 z ez)
--}




{--
eqInType-ext : {u : univs} (isu : is-universe u) {w : 𝕎·} {A B : CTerm}
               (eqt : eqTypes u w A B) → eqInTypeExt eqt
eqInType-ext {u} isu {w} {A} {B} (EQTNAT x x₁) =
  λ eqt2 a b → eqInType-⇛-NAT-rev u isu w A B a b x x₁ eqt2 , eqInType-⇛-NAT u isu w A B a b x x₁ eqt2
eqInType-ext {u} isu {w} {A} {B} (EQTQNAT x x₁) =
  {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTFREE x x₁) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  λ eqt2 a b → eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2 ,
                eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = eqInType-ext isu (eqta w1 e1)

    indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a₁ a₂ eqa = eqInType-ext isu (eqtb w1 e1 a₁ a₂ eqa)

eqInType-ext {u} isu {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt3) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTUNIV x) = {!!}
eqInType-ext {u} isu {w} {A} {B} (EQTBAR x) =
  λ eqt' a b → (λ ei → {!!}) , {!!}
  where
    ind : inbar' w x (λ w' e' eqt' → eqInTypeExt eqt')
    ind = Bar.∀𝕎-inBar-inBar' inOpenBar-Bar (λ w1 e1 z → eqInType-ext isu z) x

-- We could possibly prove it if the IH was for all lower types, not just the ones immediatly below
-- Using a relation like [<Type]
-- NOTE: this breaks the 'inbar' abstraction!
--}







{--atbar-≽ : {u : univs} (umon : mon (proj₁ (snd u)))
          {w w0 w1 : 𝕎·} (e0 : w0 ≽ w) (e1 : w1 ≽ w0) {A B : CTerm}
          (eqt : eqTypes u w0 A B)
          (i : inbar w (λ w'' _ → eqTypes u w'' A B))
          → atbar i w0 e0 eqt
          → atbar i w1 (extTrans e1 e0) (eqTypes-mon u umon eqt w1 e1)
atbar-≽ {u} umon {w} {w0} {w1} e0 e1 {A} {B} .(snd (snd (i w2 e2)) w0 e3 e0) i (ATOPENBAR w2 e2 .w0 e3 .e0) =
  {!ATOPENBAR ? ? ? ? ?!}--}



{--
<Type-PIa-EQTBAR : {u : univs} (umon : mon (proj₁ (snd u))) {w : 𝕎·} {A B A1 A2 B1 B2 : CTerm}
                   (c₁ : A ⇛ PI A1 B1 at w)
                   (c₂ : B ⇛ PI A2 B2 at w)
                   (i : inbar w (λ w'' _ → eqTypes u w'' A B))
                   (eqta : ∀𝕎 w (λ w'' _ → eqTypes u w'' A1 A2))
                   (eqtb : ∀𝕎 w (λ w'' e → (a1 a2 : CTerm) → eqInType u w'' (eqta w'' e) a1 a2
                                           → eqTypes u w'' (sub a1 B1) (sub a2 B2)))
                   (w0 : 𝕎·) (e0 : w0 ≽ w) (eqt : eqTypes u w0 A B) (a : atbar i w0 e0 eqt)
                   (w1 : 𝕎·) (e1 : w1 ≽ w0)
                   → <Type u (eqta w1 (extTrans e1 e0)) (EQTBAR i)
<Type-PIa-EQTBAR {u} umon {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ i eqta eqtb w0 e0 eqt a w1 e1 =
  <TypeS
    {!!} {!!} {!!} {!!}
    (<TypeBAR w A B i w0 e0 eqt a)
{--    (<TypeBAR
      w A B i w1 (extTrans e1 e0) (eqTypes-mon u umon eqt w1 e1) -- w0 instead of w1?
      {!!}) --}
--}



{--
eqInTypExt-∀𝕎-mon-PIa : {u : univs} {w : 𝕎·} {A B A1 A2 B1 B2 : CTerm}
                          (c₁ : A ⇛ PI A1 B1 at w)
                          (c₂ : B ⇛ PI A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w'' _ → eqTypes u w'' A1 A2))
                          (w' : 𝕎·) (e' : w' ≽ w)
                          (z : eqTypes u w' A B)
                          (ext : {w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u w' A' B') → <Type u eqt' z → eqInTypeExt eqt')
                          (w1 : 𝕎·) (e1 : w1 ≽ w')
                          → eqInTypeExt (∀𝕎-mon e' eqta w1 e1)
-- By induction on z
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTNAT x x₁) ext w1 e1 = ⊥-elim (PIneqNAT (⇛-val-det tt tt (⇛-mon e' c₁) x))
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTQNAT x x₁) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTFREE x x₁) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext w1 e1
  rewrite PIinj1 (⇛-val-det tt tt (⇛-mon e' c₁) x)
        | PIinj2 (⇛-val-det tt tt (⇛-mon e' c₁) x)
        | PIinj1 (⇛-val-det tt tt (⇛-mon e' c₂) x₁)
        | PIinj2 (⇛-val-det tt tt (⇛-mon e' c₂) x₁) =
  eqTypes-eqInTypeExt (eqta₁ w1 e1) (eqta w1 (extTrans e1 e')) (ext (eqta₁ w1 e1) (<Type1 _ _ (<TypePIa w' A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTSQUASH A3 A4 x x₁ eqtA) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTUNIV x) ext w1 e1 = {!!}
eqInTypExt-∀𝕎-mon-PIa {u} {w} {A} {B} {A1} {A2} {B1} {B2} c₁ c₂ eqta w' e' (EQTBAR x) ext w1 e1 = {!!}
--}



{--is-universe-uni : (n : ℕ) → is-universe (uni n)
is-universe-uni n w A B h = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 z → z) h--}



{--is-uni→is-universe : {u : univs} → is-uni u → is-universe u
is-uni→is-universe {u} (n , e) rewrite e = is-universe-uni (ul n)--}



{--is-uni→mon : {u : univs} → is-uni u → mon (fst (snd u))
is-uni→mon {u} (n , isu) {a} {b} {w} h w' e' rewrite isu = ↑inbar h e'--}



eqInType-⇛-UNIV->0 : (n : ℕ) (w : 𝕎·) (A B a b : CTerm)
                   → A #⇛ #UNIV n at w
                   → B #⇛ #UNIV n at w
                   → (eqt : eqTypes (uni n) w A B)
                   → (eqi : eqInType (uni n) w eqt a b)
                   → 0 < n
{-# TERMINATING #-}
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTNAT x x₁) eqi = ⊥-elim (UNIVneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTQNAT x x₁) eqi = ⊥-elim (UNIVneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (UNIVneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (UNIVneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTFREE x x₁) eqi = ⊥-elim (UNIVneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (UNIVneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (UNIVneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (UNIVneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) eqi = ⊥-elim (UNIVneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) eqi = ⊥-elim (UNIVneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) eqi = ⊥-elim (UNIVneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) eqi = ⊥-elim (UNIVneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) eqi = ⊥-elim (UNIVneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 (suc n) w A B a b c₁ c₂ (EQTUNIV m p d₁ d₂) eqi = _≤_.s≤s _≤_.z≤n
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA) eqi = ⊥-elim (UNIVneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV->0 n w A B a b c₁ c₂ (EQTBAR x) eqi =
  lower (Bar.inBar-const inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar x aw eqi))
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) → atbar x w' e' z
                         → eqInType (uni n) w' z a b
                         → Lift (lsuc Level.zero) (0 < n))
    aw w' e' z at eqi' = lift (eqInType-⇛-UNIV->0 n w' A B a b (⇛-mon e' c₁) (⇛-mon e' c₂) z eqi')



→eqInType-EQTUNIV : (n : ℕ) {w : 𝕎·} {a b : CTerm} {A B : CTerm}
                     (i : ℕ) (p : i < n)
                     (c₁ : A #⇛ #UNIV i at w)
                     (c₂ : B #⇛ #UNIV i at w)
                     → inbarEqTypes (uni i) w a b
                     → eqInType (uni n) w {A} {B} (EQTUNIV i p c₁ c₂) a b
→eqInType-EQTUNIV (suc n) {w} {a} {b} {A} {B} i p c₁ c₂ eqi with i <? n
... | yes q = →eqInType-EQTUNIV n {w} {a} {b} {A} {B} i q c₁ c₂ eqi
... | no q = d
  where
    e : n ≡ i
    e = ≤-s≤s-≡ i n (s≤s-inj p) (≮⇒≥ λ z → q (s≤s-inj z))

    d : inbarEqTypes (uni n) w a b
    d rewrite e = eqi



eqInType-EQTUNIV→ : (n : ℕ) {w : 𝕎·} {a b : CTerm} {A B : CTerm}
                     (i : ℕ) (p : i < n)
                     (c₁ : A #⇛ #UNIV i at w)
                     (c₂ : B #⇛ #UNIV i at w)
                     → eqInType (uni n) w {A} {B} (EQTUNIV i p c₁ c₂) a b
                     → inbarEqTypes (uni i) w a b
eqInType-EQTUNIV→ (suc n) {w} {a} {b} {A} {B} i p c₁ c₂ eqi with i <? n
... | yes q = eqInType-EQTUNIV→ n {w} {a} {b} {A} {B} i q c₁ c₂ eqi
... | no q = d
  where
    e : n ≡ i
    e = ≤-s≤s-≡ i n (s≤s-inj p) (≮⇒≥ λ z → q (s≤s-inj z))

    d : inbarEqTypes (uni i) w a b
    d rewrite sym e = eqi



eqInType-⇛-UNIV : (i n : ℕ) (p : i < n) (w : 𝕎·) (A B a b : CTerm)
                   → A #⇛ #UNIV i at w
                   → B #⇛ #UNIV i at w
                   → (eqt : eqTypes (uni n) w A B)
                   → (eqi : eqInType (uni n) w eqt a b)
                   → inbarEqTypes (uni i) w a b
{-# TERMINATING #-}
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTNAT x x₁) eqi = ⊥-elim (UNIVneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTQNAT x x₁) eqi = ⊥-elim (UNIVneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (UNIVneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (UNIVneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTFREE x x₁) eqi = ⊥-elim (UNIVneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (UNIVneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (UNIVneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (UNIVneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) eqi = ⊥-elim (UNIVneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) eqi = ⊥-elim (UNIVneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) eqi = ⊥-elim (UNIVneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) eqi = ⊥-elim (UNIVneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) eqi = ⊥-elim (UNIVneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i (suc n) p w A B a b c₁ c₂ (EQTUNIV m q d₁ d₂) eqi = c'
  where
    c : inbarEqTypes (uni m) w a b
    c = eqInType-EQTUNIV→ (suc n) {w} {a} {b} {A} {B} m q d₁ d₂ eqi

    c' : inbarEqTypes (uni i) w a b
    c' rewrite UNIVinj (⇛-val-det tt tt c₁ d₁) = c

eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTLIFT A1 A2 x x₁ eqtA) eqi = ⊥-elim (UNIVneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNIV i n p w A B a b c₁ c₂ (EQTBAR x) eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) → atbar x w' e' z
                         → eqInType (uni n) w' z a b
                         → inbar w' (↑wPred' (λ w'' e → eqTypes (uni i) w'' a b) e'))
    aw w' e' z at eqi' = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' z xt → z) j
      where
        j : inbar w' (λ w'' e → eqTypes (uni i) w'' a b)
        j = eqInType-⇛-UNIV i n p w' A B a b (⇛-mon e' c₁) (⇛-mon e' c₂) z eqi'




{--inbar-eqTypes-pred→eqInUnivi : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                (p : 0 < n)
                                (i : inbar w (λ w' _ → eqTypes (uni (pred n)) w' a b))
                                → eqInUnivi n w a b
inbar-eqTypes-pred→eqInUnivi {suc n} {w} {a} {b} p i = i--}




{--is-uni-eqInType-EQTUNIV→ : {u : univs} (isu : is-uni u) {w : 𝕎·} {a b : CTerm} {A B : CTerm}
                            (x : fst (snd u) w A B)
                            → eqInType u w (EQTUNIV x) a b
                            → eqInUnivi (fst isu) w a b
is-uni-eqInType-EQTUNIV→ {u} (n , isu) {w} {a} {b} {A} {B} x eqi rewrite isu = eqi--}



{--is-uni→eqUnivi : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
                  (x : fst (snd u) w A B)
                  → eqUnivi (fst isu) w A B
is-uni→eqUnivi {u} (n , isu) {w} {A} {B} x rewrite isu = x--}




eqInType-ext-bar : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
                   (i : inbar w (λ w' _ → eqTypes u w' A B))
                   → (ind : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → <Type {u'} eqt' {(u , isu)} (EQTBAR i) → eqInTypeExt eqt')
                   → (a b : CTerm)
                   → inbar' w i (λ w' e' z → eqInType u w' z a b)
                   → (eqt : eqTypes u w A B) → eqInType u w eqt a b
eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTNAT x x₁) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → #strongMonEq w'' a b) e'))
    aw w' e' z at eqt' =
      Bar.∀𝕎-inBarFunc
        inOpenBar-Bar
        (λ w1 e1 s ext → s)
        (eqInType-⇛-NAT u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) z eqt')

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTQNAT x x₁) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → #weakMonEq w'' a b) e'))
    aw w' e' z at eqt' =
      Bar.∀𝕎-inBarFunc
        inOpenBar-Bar
        (λ w1 e1 s ext → s)
        (eqInType-⇛-QNAT u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) z eqt')

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w' e' z at eqt' =
      Bar.∀𝕎-inBarFunc
        inOpenBar-Bar
        (λ w1 e1 s ext → s)
        (eqInType-⇛-LT u w' A B a1 b1 a2 b2 a b (⇛-mon e' x) (⇛-mon e' x₁) z eqt')

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w' e' z at eqt' =
      Bar.∀𝕎-inBarFunc
        inOpenBar-Bar
        (λ w1 e1 s ext → s)
        (eqInType-⇛-QLT u w' A B a1 b1 a2 b2 a b (⇛-mon e' x) (⇛-mon e' x₁) z eqt')

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTFREE x x₁) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → #⇛to-same-CS w'' a b) e'))
    aw w' e' z at eqt' =
      Bar.∀𝕎-inBarFunc
        inOpenBar-Bar
        (λ w1 e1 s ext → s)
        (eqInType-⇛-FREE u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) z eqt')

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → PIeq (eqInType u w'' (eqta w'' e)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' e a1 a2 eqa)) a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-PI2
          u w' A B A1 A2 B1 B2 a b
          (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
          (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR (u , isu) w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR (u , isu) w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → PIeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) a b
                                 → ↑wPred' (λ w''' e → PIeq (eqInType u w''' (eqta w''' e)) (λ a1 a2 eqa → eqInType u w''' (eqtb w''' e a1 a2 eqa)) a b) e' w'' e'')
        aw1 w1 e1 h ext = PIeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → SUMeq (eqInType u w'' (eqta w'' e)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' e a1 a2 eqa)) w'' a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-SUM2
          u w' A B A1 A2 B1 B2 a b
          (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
          (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR u w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR u w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → SUMeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) w'' a b
                                 → ↑wPred' (λ w''' e → SUMeq (eqInType u w''' (eqta w''' e)) (λ a1 a2 eqa → eqInType u w''' (eqtb w''' e a1 a2 eqa)) w'' a b) e' w'' e'')
        aw1 w1 e1 h ext = SUMeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b → inbar w' (↑wPred' (λ w'' e → SETeq (eqInType u w'' (eqta w'' e)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' e a1 a2 eqa)) a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-SET2
          u w' A B A1 A2 B1 B2 a b
          (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
          (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR u w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR u w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → SETeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) a b
                                 → ↑wPred' (λ w''' e → SETeq (eqInType u w''' (eqta w''' e)) (λ a1 a2 eqa → eqInType u w''' (eqtb w''' e a1 a2 eqa)) a b) e' w'' e'')
        aw1 w1 e1 h ext = SETeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} exta extb h

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta exta eqt1 eqt2) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b
                         → inbar w' (↑wPred' (λ w'' e → EQeq a1 a2 (eqInType u w'' (eqta w'' e)) w'' a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-EQ2
          u w' A B A₁ B₁ a1 b1 a2 b2 a b
          (∀𝕎-mon e' eqta)
          (wPredExtIrr-eqInType-mon eqta exta w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR u w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR u w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → EQeq a1 a2 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → ↑wPred' (λ w''' e → EQeq a1 a2 (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e'')
        aw1 w1 e1 h ext = EQeq-ext {u} {w} {A₁} {B₁} {a1} {a2} {eqta} {_} {_} {_} {a} {b} exta h

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b
                         → inbar w' (↑wPred' (λ w'' e → UNIONeq (eqInType u w'' (eqta w'' e)) (eqInType u w'' (eqtb w'' e)) w'' a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-UNION2
          u w' A B A1 A2 B1 B2 a b
          (∀𝕎-mon e' eqta)
          (∀𝕎-mon e' eqtb)
          (wPredExtIrr-eqInType-mon eqta exta w' e')
          (wPredExtIrr-eqInType-mon eqtb extb w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR u w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR u w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → UNIONeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (eqInType u w'' (∀𝕎-mon e' eqtb w'' e'')) w'' a b
                                 → ↑wPred' (λ w''' e → UNIONeq (eqInType u w''' (eqta w''' e)) (eqInType u w''' (eqtb w''' e)) w''' a b) e' w'' e'')
        aw1 w1 e1 h ext = UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTSQUASH A1 A2 x x₁ eqta exta) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b
                         → inbar w' (↑wPred' (λ w'' e → TSQUASHeq (eqInType u w'' (eqta w'' e)) w'' a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-TSQUASH2
          u w' A B A1 A2 a b
          (∀𝕎-mon e' eqta)
          (wPredExtIrr-eqInType-mon eqta exta w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR u w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR u w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → ↑wPred' (λ w''' e → TSQUASHeq (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e'')
        aw1 w1 e1 h ext = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h

--eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTDUM A1 A2 x x₁ eqt) = lift tt

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) → atbar i w' e' z → eqInType u w' z a b
                         → inbar w' (↑wPred' (λ w'' e → FFDEFSeq x1 (eqInType u w'' (eqta w'' e)) w'' a b) e'))
    aw w' e' z at eqi =
      Bar.∀𝕎-inBarFunc inOpenBar-Bar
        aw1
        (eqInType-⇛-FFDEFS2
          u w' A B A1 A2 x1 x2 a b
          (∀𝕎-mon e' eqta)
          (wPredExtIrr-eqInType-mon eqta exta w' e')
          (⇛-mon e' x) (⇛-mon e' x₁) z eqi ind')

      where
        ind' : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u , isu} z → eqInTypeExt eqt'
        ind' {u'} {w''} {A'} {B'} eqt' (≤Type0 .eqt') = ind eqt' (<Type1 _ _ (<TypeBAR u w A B i w' e' z at))
        ind' {u'} {w''} {A'} {B'} eqt' (≤TypeS .eqt' .z x) = ind eqt' (<TypeS _ _ _ x (<TypeBAR u w A B i w' e' z at))

        aw1 : ∀𝕎 w' (λ w'' e'' → FFDEFSeq x1 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → ↑wPred' (λ w''' e → FFDEFSeq x1 (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e'')
        aw1 w1 e1 h ext = FFDEFSeq-ext {u} {w} {A1} {A2} {x1} {eqta} {_} {_} {_} {a} {b} exta h

eqInType-ext-bar {u} (n , isu) {w} {A} {B} i ind a b j (EQTUNIV m p d₁ d₂) rewrite isu =
  →eqInType-EQTUNIV n {w} {a} {b} {A} {B} m p d₁ d₂ c
  where
    j' : inbar' w i (λ w' e' z → eqInType (uni n) w' z a b)
    j' = j

    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) → atbar i w' e' z
                             → eqInType (uni n) w' z a b
                             → inbar w' (↑wPred' (λ w'' _ → eqTypes (uni m) w'' a b) e'))
    aw w' e' z at eqt = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' z x → z) ib
      where
        ib : inbar w' (λ w'' _ → eqTypes (uni m) w'' a b)
        ib = eqInType-⇛-UNIV m n p w' A B a b (⇛-mon e' d₁) (⇛-mon e' d₂) z eqt

    c : inbarEqTypes (uni m) w a b
    c = Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTLIFT A1 A2 x x₁ eqta) = {!!}

eqInType-ext-bar {u} isu {w} {A} {B} i ind a b j (EQTBAR x) =
  Bar.inBar'-change inOpenBar-Bar i x aw j
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : eqTypes u w' A B)
                         → atbar i w' e' x₁
                         → atbar x w' e' x₂
                         → eqInType u w' x₁ a b
                         → eqInType u w' x₂ a b)
    aw w1 e1 x₁ x₂ a₁ a₂ ei = fst (ext x₂ a b) ei
      where
        ext : eqInTypeExt x₁
        ext = ind x₁ (<Type1 _ _ (<TypeBAR _ _ _ _ i w1 e1 x₁ a₁))




{--
data ¬bar (u : univs) {w : 𝕎·} {T1 T2 : CTerm} : eqTypes u w T1 T2 → Set
data ¬bar u {w} {T1} {T2} where
  ¬bar-NAT : (c₁ : T1 ⇛ NAT at w) (c₂ : T2 ⇛ NAT at w) → ¬bar u (EQTNAT c₁ c₂)
  ¬bar-QNAT : (c₁ : T1 ⇛ QNAT at w) (c₂ : T2 ⇛ QNAT at w) → ¬bar u (EQTQNAT c₁ c₂)
  ¬bar-LT : (a1 a2 b1 b2 : CTerm)
            (c₁ : T1 ⇛ (LT a1 b1) at w) (c₂ : T2 ⇛ (LT a2 b2) at w)
            (s₁ : strongMonEq w a1 a2) (s₂ : strongMonEq w b1 b2)
            → ¬bar u (EQTLT a1 a2 b1 b2 c₁ c₂ s₁ s₂)
  ¬bar-QLT : (a1 a2 b1 b2 : CTerm)
             (c₁ : T1 ⇛ (QLT a1 b1) at w) (c₂ : T2 ⇛ (QLT a2 b2) at w)
             (w₁ : weakMonEq w a1 a2) (w₂ : weakMonEq w b1 b2)
             → ¬bar u (EQTQLT a1 a2 b1 b2 c₁ c₂ w₁ w₂)
  ¬bar-FREE : (c₁ : T1 ⇛ FREE at w) (c₂ : T2 ⇛ FREE at w) → ¬bar u (EQTFREE c₁ c₂)
  ¬bar-PI : (A1 B1 A2 B2 : CTerm)
            (c₁ : T1 ⇛ (PI A1 B1) at w) (c₂ : T2 ⇛ (PI A2 B2) at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub a1 B1) (sub a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            → ¬bar u (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  ¬bar-SUM : (A1 B1 A2 B2 : CTerm)
             (c₁ : T1 ⇛ (SUM A1 B1) at w) (c₂ : T2 ⇛ (SUM A2 B2) at w)
             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub a1 B1) (sub a2 B2)))
             → ¬bar u (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  ¬bar-SET : (A1 B1 A2 B2 : CTerm)
             (c₁ : T1 ⇛ (SET A1 B1) at w) (c₂ : T2 ⇛ (SET A2 B2) at w)
             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub a1 B1) (sub a2 B2)))
             → ¬bar u (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  ¬bar-EQ : (a1 b1 a2 b2 A B : CTerm)
            (c₁ : T1 ⇛ (EQ a1 a2 A) at w) (c₂ : T2 ⇛ (EQ b1 b2 B) at w)
            (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A B))
            (eqt1 : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
            (eqt2 : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
            → ¬bar u (EQTEQ a1 b1 a2 b2 A B c₁ c₂ eqtA eqt1 eqt2)
  ¬bar-UNION : (A1 B1 A2 B2 : CTerm)
               (c₁ : T1 ⇛ (UNION A1 B1) at w) (c₂ : T2 ⇛ (UNION A2 B2) at w)
               (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
               (eqtB : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
               → ¬bar u (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB)
  ¬bar-SQUASH : (A1 A2 : CTerm)
                (c₁ : T1 ⇛ (TSQUASH A1) at w) (c₂ : T2 ⇛ (TSQUASH A2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                → ¬bar u (EQTSQUASH A1 A2 c₁ c₂ eqtA)
  ¬bar-FFDEFS : (A1 A2 x1 x2 : CTerm)
                (c₁ : T1 ⇛ (FFDEFS A1 x1) at w) (c₂ : T2 ⇛ (FFDEFS A2 x2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (eqx : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) x1 x2))
                → ¬bar u (EQFFDEFS A1 A2 x1 x2 c₁ c₂ eqtA eqx)
  ¬bar-UNIV : (c : proj₁ (proj₂ u) w T1 T2) → ¬bar u (EQTUNIV c)
--}


{--
-- direct proof?
collapseBars-eqInType : {u : univs} (isu : is-universe u) {w : 𝕎·} {A B : CTerm}
                        (i : inbar w (λ w' _ → eqTypes u w' A B))
                        (ext : {w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u w' A' B') → <Type u eqt' (EQTBAR i) → eqInTypeExt eqt')
                        {a b : CTerm}
                        (j : inbar' w i (λ w' e' z → eqInType u w' z a b))
                        → inbar' w i (λ w' e' z → eqInType u w' z a b × ¬bar u z)
collapseBars-eqInType {u} isu {w} {A} {B} i ext {a} {b} j = {!!}

  Bar.inBar'-idem inOpenBar-Bar i k
  where
    aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' A B) → atbar i w' e' x
                         → eqInType u w' x a b
                         → inbar' w' (↑'inbar i e') (↑wPredDep' (λ w'' e'' z → eqInType u w'' z a b × ¬bar u z) e'))
    aw w1 e1 (EQTNAT x x₁) at ei =
      Bar.∀𝕎-inBar-inBar' inOpenBar-Bar {!!} (↑'inbar i e1)
      where
        aw0 : ∀𝕎 w1 (λ w' e' → (x₂ : ↑wPred' (λ w'' e → eqTypes u w'' A B) e1 w' e') →  w')
    aw w1 e1 (EQTQNAT x x₁) at ei = {!!}
    aw w1 e1 (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) at ei = {!!}
    aw w1 e1 (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) at ei = {!!}
    aw w1 e1 (EQTFREE x x₁) at ei = {!!}
    aw w1 e1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) at ei = {!!}
    aw w1 e1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) at ei = {!!}
    aw w1 e1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) at ei = {!!}
    aw w1 e1 (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) at ei = {!!}
    aw w1 e1 (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) at ei = {!!}
    aw w1 e1 (EQTSQUASH A1 A2 x x₁ eqtA) at ei = {!!}
    aw w1 e1 (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) at ei = {!!}
    aw w1 e1 (EQTUNIV x) at ei = {!!}
    aw w1 e1 (EQTBAR x) at ei = {!!}

    k : inbar w (λ w' e' → inbar' w' (↑'inbar i e') (↑wPredDep' (λ w' e' z → eqInType u w' z a b × ¬bar u z) e'))
    k = Bar.∀𝕎-inBar'-inBar2 inOpenBar-Bar i aw j
--}



{--eqInUnivi-mon : (n : ℕ) → mon (eqInUnivi n)
eqInUnivi-mon (suc n) {a} {b} {w} eqi w' e' =
  Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' z → z) (↑inbar eqi e')--}



uniUpTo-mon : {n i : ℕ} {p : i < n} → mon (uniUpTo n i p)
uniUpTo-mon {suc n} {i} {p} {w} eqt w' e with i <? n
... | yes q = uniUpTo-mon {n} {i} {q} {w} eqt w' e
... | no q = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' z → z) (↑inbar eqt e)


uniUpTo→inbarEqTypes : {i n : ℕ} {p : i < n} {w : 𝕎·} {a b : CTerm}
                        → uniUpTo n i p w a b
                        → inbarEqTypes (uni i) w a b
uniUpTo→inbarEqTypes {i} {suc n} {p} {w} {a} {b} eqi with i <? n
... | yes q = uniUpTo→inbarEqTypes {i} {n} {q} {w} {a} {b} eqi
... | no q = d
  where
    e : n ≡ i
    e = ≤-s≤s-≡ i n (s≤s-inj p) (≮⇒≥ λ z → q (s≤s-inj z))

    d : inbarEqTypes (uni i) w a b
    d rewrite sym e = eqi



inbarEqTypes→uniUpTo : {i n : ℕ} {p : i < n} {w : 𝕎·} {a b : CTerm}
                        → inbarEqTypes (uni i) w a b
                        → uniUpTo n i p w a b
inbarEqTypes→uniUpTo {i} {suc n} {p} {w} {a} {b} eqi with i <? n
... | yes q = inbarEqTypes→uniUpTo {i} {n} {q} {w} {a} {b} eqi
... | no q = d
  where
    e : n ≡ i
    e = ≤-s≤s-≡ i n (s≤s-inj p) (≮⇒≥ λ z → q (s≤s-inj z))

    d : inbarEqTypes (uni n) w a b
    d rewrite e = eqi



uniUpTo-<irr : {i n : ℕ} {p q : i < n} {w : 𝕎·} {a b : CTerm}
               → uniUpTo n i p w a b
               → uniUpTo n i q w a b
uniUpTo-<irr {i} {n} {p} {q} {w} {a} {b} e = inbarEqTypes→uniUpTo {i} {n} {q} (uniUpTo→inbarEqTypes {i} {n} {p} e)




_B#⇛_at_ : (T T' : CTerm) (w : 𝕎·) → Set₁
T B#⇛ T' at w = inbar w (λ w' _ → T #⇛ T' at w')
infix 30 _B#⇛_at_


_B⇛_at_ : (T T' : Term) (w : 𝕎·) → Set₁
T B⇛ T' at w = inbar w (λ w' _ → T ⇛ T' at w')
infix 30 _B⇛_at_


#⇛-mon : {a b : CTerm} {w2 w1 : 𝕎·} → w1 ⊑· w2 → a #⇛ b at w1 → a #⇛ b at w2
#⇛-mon {a} {b} {w2} {w1} e c = ⇛-mon e c


B#⇛-mon : {a b : CTerm} {w2 w1 : 𝕎·} → w1 ⊑· w2 → a B#⇛ b at w1 → a B#⇛ b at w2
B#⇛-mon {a} {b} {w2} {w1} e c = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' z → z) (Bar.↑inBar inOpenBar-Bar c e)


#⇛→B#⇛ : {a b : CTerm} {w : 𝕎·} → a #⇛ b at w → a B#⇛ b at w
#⇛→B#⇛ {a} {b} {w} c = Bar.∀𝕎-inBar inOpenBar-Bar (λ w' e' → #⇛-mon {a} {b} e' c)


Bₗ#⇛-val-det : {w : 𝕎·} {a v₁ v₂ : CTerm} → #isValue v₁ → #isValue v₂ → a B#⇛ v₁ at w → a #⇛ v₂ at w → ⌜ v₁ ⌝ ≡ ⌜ v₂ ⌝
Bₗ#⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ =
  lower (Bar.inBar-const inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw c₁))
  where
    aw : ∀𝕎 w (λ w' e' → a #⇛ v₁ at w' → Lift 1ℓ (⌜ v₁ ⌝ ≡ ⌜ v₂ ⌝))
    aw w' e' c = lift (≡CTerm {v₁} {v₂} (#⇛-val-det {w'} {a} {v₁} {v₂} isv₁ isv₂ c (⇛-mon e' c₂)))



Bₗ⇛-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a B⇛ v₁ at w → a ⇛ v₂ at w → v₁ ≡ v₂
Bₗ⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ =
  lower (Bar.inBar-const inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw c₁))
  where
    aw : ∀𝕎 w (λ w' e' → a ⇛ v₁ at w' → Lift 1ℓ (v₁ ≡ v₂))
    aw w' e' c = lift (⇛-val-det isv₁ isv₂ c (⇛-mon e' c₂))



Bᵣ#⇛-val-det : {w : 𝕎·} {a v₁ v₂ : CTerm} → #isValue v₁ → #isValue v₂ → a #⇛ v₁ at w → a B#⇛ v₂ at w → ⌜ v₁ ⌝ ≡ ⌜ v₂ ⌝
Bᵣ#⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ = sym (Bₗ#⇛-val-det {w} {a} {v₂} {v₁}  isv₂ isv₁ c₂ c₁)



Bᵣ⇛-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇛ v₁ at w → a B⇛ v₂ at w → v₁ ≡ v₂
Bᵣ⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ = sym (Bₗ⇛-val-det isv₂ isv₁ c₂ c₁)



eqInType-u-bar : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
                 (c₁ : A B#⇛ (#UNIV i) at w)
                 (c₂ : B B#⇛ (#UNIV i) at w)
                 (eqt : eqTypes (uni n) w A B)
                 (a b : CTerm)
                 (eqi : uniUpTo n i p w a b)
                 → eqInType (uni n) w eqt a b
{-# TERMINATING #-}
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTNAT x x₁) a b eqi = ⊥-elim (UNIVneqNAT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTQNAT x x₁) a b eqi = ⊥-elim (UNIVneqQNAT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) a b eqi = ⊥-elim (UNIVneqLT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) a b eqi = ⊥-elim (UNIVneqQLT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTFREE x x₁) a b eqi = ⊥-elim (UNIVneqFREE (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) a b eqi = ⊥-elim (UNIVneqPI (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) a b eqi = ⊥-elim (UNIVneqSUM (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) a b eqi = ⊥-elim (UNIVneqSET (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) a b eqi = ⊥-elim (UNIVneqEQ (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (UNIVneqUNION (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqta exta) a b eqi = ⊥-elim (UNIVneqTSQUASH (Bₗ⇛-val-det tt tt c₁ x))
--eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) a b eqi = ⊥-elim (lower (Bar.inBar-const inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' (c₁ , c₂) → lift (UNIVneqDUM (Bₗ⇛-val-det tt tt c₁ (⇛-mon e' x)))) i)))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) a b eqi = ⊥-elim (UNIVneqFFDEFS (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTUNIV m q d₁ d₂) a b eqi rewrite UNIVinj (Bₗ⇛-val-det tt tt c₁ d₁) = uniUpTo-<irr {m} {n} {p} {q} eqi
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTLIFT A1 A2 x x₁ eqta) a b eqi = ⊥-elim (UNIVneqLIFT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTBAR x) a b eqi = c
  where
    c : inbar' w x (λ w' _ (z : eqTypes (uni n) w' A B) → eqInType (uni n) w' z a b)
    c = Bar.∀𝕎-inBar-inBar' inOpenBar-Bar x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) (at : atbar x w' e' z) → eqInType (uni n) w' z a b)
        aw w' e' equ at = eqInType-u-bar p (B#⇛-mon {A} {#UNIV i} e' c₁) (B#⇛-mon {B} {#UNIV i} e' c₂) equ a b (uniUpTo-mon {n} {i} {p} eqi w' e')




eqInType-u : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
             (c₁ : A #⇛ (#UNIV i) at w)
             (c₂ : B #⇛ (#UNIV i) at w)
             (eqt : eqTypes (uni n) w A B)
             (a b : CTerm)
             (eqi : uniUpTo n i p w a b)
             → eqInType (uni n) w eqt a b
eqInType-u {i} {n} p {w} {A} {B} c₁ c₂ eqt a b eqi =
  eqInType-u-bar p (#⇛→B#⇛ {A} {#UNIV i} c₁) (#⇛→B#⇛ {B} {#UNIV i} c₂) eqt a b eqi



eqInType-u-rev-bar : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
                     (c₁ : A B#⇛ #UNIV i at w)
                     (c₂ : B B#⇛ #UNIV i at w)
                     (eqt : eqTypes (uni n) w A B)
                     (a b : CTerm)
                     (eqi : eqInType (uni n) w eqt a b)
                     → uniUpTo n i p w a b
{-# TERMINATING #-}
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTNAT x x₁) a b eqi = ⊥-elim (UNIVneqNAT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTQNAT x x₁) a b eqi = ⊥-elim (UNIVneqQNAT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) a b eqi = ⊥-elim (UNIVneqLT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) a b eqi = ⊥-elim (UNIVneqQLT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTFREE x x₁) a b eqi = ⊥-elim (UNIVneqFREE (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) a b eqi = ⊥-elim (UNIVneqPI (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) a b eqi = ⊥-elim (UNIVneqSUM (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) a b eqi = ⊥-elim (UNIVneqSET (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) a b eqi = ⊥-elim (UNIVneqEQ (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (UNIVneqUNION (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqta exta) a b eqi = ⊥-elim (UNIVneqTSQUASH (Bₗ⇛-val-det tt tt c₁ x))
--eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) a b eqi = ⊥-elim (lower (Bar.inBar-const inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' (c₁ , c₂) → lift (UNIVneqDUM (Bₗ⇛-val-det tt tt c₁ (⇛-mon e' x)))) i)))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) a b eqi = ⊥-elim (UNIVneqFFDEFS (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTUNIV m q d₁ d₂) a b eqi rewrite UNIVinj (Bₗ⇛-val-det tt tt c₁ d₁) = uniUpTo-<irr {m} {n} {q} {p} eqi
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTLIFT A1 A2 x x₁ eqta) a b eqi = ⊥-elim (UNIVneqLIFT (Bₗ⇛-val-det tt tt c₁ x))
eqInType-u-rev-bar {i} {n} p {w} {A} {B} c₁ c₂ (EQTBAR x) a b eqi = inbarEqTypes→uniUpTo {i} {n} {p} {w} {a} {b} c
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) (at : atbar x w' e' z)
                         → eqInType (uni n) w' z a b
                         → inbar w' (↑wPred' (λ w'' e → eqTypes (uni i) w'' a b) e'))
    aw w' e' z at eqi' = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 eqt' z → eqt')
                                          (uniUpTo→inbarEqTypes {i} {n} {p} {w'} {a} {b} (eqInType-u-rev-bar p (B#⇛-mon {A} {#UNIV i} e' c₁) (B#⇛-mon {B} {#UNIV i} e' c₂) z a b eqi'))

    c : inbarEqTypes (uni i) w a b
    c = Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar x aw eqi)


eqInType-u-rev : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
                 (c₁ : A #⇛ (#UNIV i) at w)
                 (c₂ : B #⇛ (#UNIV i) at w)
                 (eqt : eqTypes (uni n) w A B)
                 (a b : CTerm)
                 (eqi : eqInType (uni n) w eqt a b)
                 → uniUpTo n i p w a b
eqInType-u-rev {i} {n} p {w} {A} {B} c₁ c₂ eqt a b eqi =
  eqInType-u-rev-bar p (#⇛→B#⇛ {A} {#UNIV i} c₁) (#⇛→B#⇛ {B} {#UNIV i} c₂) eqt a b eqi



{--eqInType-u-rev2 : {u : univs} {w : 𝕎·} {A B : CTerm}
                  (isu : is-uni u)
                  (i : fst (snd u) w A B)
                  (eqt : eqTypes u w A B)
                  (a b : CTerm)
                  (eqi : eqInType u w eqt a b)
                  → eqInType u w (EQTUNIV i) a b
eqInType-u-rev2 {u} {w} {A} {B} (n , isu) i eqt a b eqi rewrite isu = eqInType-u-rev i eqt a b eqi
--}




eqInTypeExt-EQTUNIV : {n : ℕ} {w : 𝕎·} {A B : CTerm}
                      (i : ℕ) (p : i < n)
                      (c₁ : A #⇛ #UNIV i at w)
                      (c₂ : B #⇛ #UNIV i at w)
                      → eqInTypeExt {uni n} {w} {A} {B} (EQTUNIV i p c₁ c₂)
eqInTypeExt-EQTUNIV {n} {w} {A} {B} i p c₁ c₂ eqt' a b =
  eqInType-u p c₁ c₂ eqt' a b , eqInType-u-rev p c₁ c₂ eqt' a b



{--
eqInType-mon : {u : univs} (umon : mon (fst (snd u))) {w : 𝕎·} {A B : CTerm}
               (eqt : eqTypes u w A B) {a b : CTerm} (w' : 𝕎·) (e' : w' ≽ w)
               → eqInType u w eqt a b
               → eqInType u w' (eqTypes-mon u umon eqt w' e') a b
eqInType-mon {u} umon {w} {A} {B} eqt {a} {b} w' e' eqi = {!!}
--}





{--
subst-eqUnivi : {u : univs} {n : ℕ} (e : u ≡ uni (suc n))
                (x : proj₁ (snd u) w A B)
                → inbar w' (λ w'' _ → A #⇛ #UNIV (suc n) at w'' × B #⇛ #UNIV (suc n) at w'')
--}



eqInType-ext-bar-rev : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
                       (i : inbar w (λ w' _ → eqTypes u w' A B))
                       → (ind : {u' : univs} {w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u' w' A' B') → <Type {u'} eqt' (EQTBAR i) → eqInTypeExt eqt')
                       → (a b : CTerm)
                       → (eqt : eqTypes u w A B)
                       → eqInType u w eqt a b
                       → inbar' w i (λ w' e' z → eqInType u w' z a b)
eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTNAT x x₁) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at = eqInType-⇛-NAT-rev u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) z ei
      where
        ei : inbar w' (λ w'' e → #strongMonEq w'' a b)
        ei = ↑inbar eqi e'

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTQNAT x x₁) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at = eqInType-⇛-QNAT-rev u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) z ei
      where
        ei : inbar w' (λ w'' e → #weakMonEq w'' a b)
        ei = ↑inbar eqi e'

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at = eqInType-⇛-LT-rev u w' A B a1 b1 a2 b2 a b (⇛-mon e' x) (⇛-mon e' x₁) z ei
      where
        ei : inbar w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
        ei = ↑inbar eqi e'

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at = eqInType-⇛-QLT-rev u w' A B a1 b1 a2 b2 a b (⇛-mon e' x) (⇛-mon e' x₁) z ei
      where
        ei : inbar w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
        ei = ↑inbar eqi e'

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTFREE x x₁) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at = eqInType-⇛-FREE-rev u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) z ei
      where
        ei : inbar w' (λ w'' e → #⇛to-same-CS w'' a b)
        ei = ↑inbar eqi e'

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-PI-rev2
        u w' A B A1 A2 B1 B2 a b
        (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → (a₁ b₁ : CTerm) (e₁ : eqInType u w''' (eqta w''' e) a₁ b₁) → eqInType u w''' (eqtb w''' e a₁ b₁ e₁) (#APPLY a a₁) (#APPLY b b₁)) e' w'' e''
                                → PIeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) a b)
        aw' w1 e1 h a₁ a₂ eqa = h a₁ a₂ eqa

        ib : inbar w' (λ w'' e → PIeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e a₁ a₂ eqa)) a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-SUM-rev2
        u w' A B A1 A2 B1 B2 a b
        (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → SUMeq (eqInType u w''' (eqta w''' e)) (λ a₁ a₂ eqa → eqInType u w''' (eqtb w''' e a₁ a₂ eqa)) w''' a b) e' w'' e''
                                 → SUMeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) w'' a b)
        aw' w1 e1 h = SUMeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

        ib : inbar w' (λ w'' e → SUMeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e a₁ a₂ eqa)) w'' a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-SET-rev2
        u w' A B A1 A2 B1 B2 a b
        (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → SETeq (eqInType u w''' (eqta w''' e)) (λ a₁ a₂ eqa → eqInType u w''' (eqtb w''' e a₁ a₂ eqa)) a b) e' w'' e''
                                 → SETeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) a b)
        aw' w1 e1 h = SETeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} exta extb h

        ib : inbar w' (λ w'' e → SETeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e a₁ a₂ eqa)) a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta exta eqt1 eqt2) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-EQ-rev2
        u w' A B A₁ B₁ a1 b1 a2 b2 a b
        (∀𝕎-mon e' eqta)
        (wPredExtIrr-eqInType-mon eqta exta w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → EQeq a1 a2 (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                                 → EQeq a1 a2 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
        aw' w1 e1 h = EQeq-ext {u} {w} {A₁} {B₁} {a1} {a2} {eqta} {_} {_} {_} {a} {b} exta h

        ib : inbar w' (λ w'' e → EQeq a1 a2 (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-UNION-rev2
        u w' A B A1 A2 B1 B2 a b
        (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w' e')
        (wPredExtIrr-eqInType-mon eqtb extb w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → UNIONeq (eqInType u w''' (eqta w''' e)) (eqInType u w''' (eqtb w''' e)) w''' a b) e' w'' e''
                                 → UNIONeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (eqInType u w'' (∀𝕎-mon e' eqtb w'' e'')) w'' a b)
        aw' w1 e1 h = UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

        ib : inbar w' (λ w'' e → UNIONeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (eqInType u w'' (∀𝕎-mon e' eqtb w'' e)) w'' a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTSQUASH A1 A2 x x₁ eqta exta) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-TSQUASH-rev2
        u w' A B A1 A2 a b
        (∀𝕎-mon e' eqta)
        (wPredExtIrr-eqInType-mon eqta exta w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → TSQUASHeq (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                                 → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
        aw' w1 e1 h = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h

        ib : inbar w' (λ w'' e → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

--eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTDUM A1 A2 x x₁ eqtA) eqi = {!!}
eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) eqi =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-FFDEFS-rev2
        u w' A B A1 A2 x1 x2 a b
        (∀𝕎-mon e' eqta)
        (wPredExtIrr-eqInType-mon eqta exta w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → FFDEFSeq x1 (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                                 → FFDEFSeq x1(eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
        aw' w1 e1 h = FFDEFSeq-ext {u} {w} {A1} {A2} {x1} {eqta} {_} {_} {_} {a} {b} exta h

        ib : inbar w' (λ w'' e → FFDEFSeq x1 (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')

eqInType-ext-bar-rev {u} (n , isu) {w} {A} {B} i ind a b (EQTUNIV m p c₁ c₂) eqi rewrite isu =
  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) (at : atbar i w' e' z) → eqInType (uni n) w' z a b)
    aw w' e' z at = ei
      where
        ei : eqInType (uni n) w' z a b
        ei = eqInType-u p {w'} {A} {B} (⇛-mon e' c₁) (⇛-mon e' c₂) z a b (uniUpTo-mon {n} {m} {p} eqi w' e')

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTLIFT A1 A2 x x₁ eqta) eqi = ?
{--  Bar.∀𝕎-inBar-inBar' inOpenBar-Bar i aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b)
    aw w' e' z at =
      eqInType-⇛-TSQUASH-rev2
        u w' A B A1 A2 a b
        (∀𝕎-mon e' eqta)
        (wPredExtIrr-eqInType-mon eqta exta w' e')
        (⇛-mon e' x) (⇛-mon e' x₁) z (<Type-EQTBAR-eqInTypeExt at ind) ib
      where
        aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → TSQUASHeq (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                                 → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
        aw' w1 e1 h = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h

        ib : inbar w' (λ w'' e → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
        ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' (↑inbar eqi e')
--}

eqInType-ext-bar-rev {u} isu {w} {A} {B} i ind a b (EQTBAR x) eqi =
  Bar.inBar'-change inOpenBar-Bar x i aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ y : eqTypes u w' A B) (at1 : atbar x w' e' x₁) (at2 : atbar i w' e' y)
                         → eqInType u w' x₁ a b
                         → eqInType u w' y a b)
    aw w' e' x₁ y at1 at2 eqi' = snd (ind y (<Type1 _ _ (<TypeBAR u w A B i w' e' y at2)) x₁ a b) eqi'




eqInType-ext0 : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B)
                → ({u' : univs} {w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u' w' A' B') → <Type {u'} eqt' eqt → eqInTypeExt eqt')
                → eqInTypeExt eqt
eqInType-ext0 {u} isu {w} {A} {B} (EQTNAT x x₁) ind =
  λ eqt2 a b → eqInType-⇛-NAT-rev u w A B a b x x₁ eqt2 ,
                eqInType-⇛-NAT u w A B a b x x₁ eqt2

eqInType-ext0 {u} isu {w} {A} {B} (EQTQNAT x x₁) ind =
  λ eqt2 a b → eqInType-⇛-QNAT-rev u w A B a b x x₁ eqt2 ,
                eqInType-⇛-QNAT u w A B a b x x₁ eqt2

eqInType-ext0 {u} isu {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind =
  λ eqt2 a b → eqInType-⇛-LT-rev u w A B a1 b1 a2 b2 a b x x₁ eqt2 ,
                eqInType-⇛-LT u w A B a1 b1 a2 b2 a b x x₁ eqt2

eqInType-ext0 {u} isu {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind =
  λ eqt2 a b → eqInType-⇛-QLT-rev u w A B a1 b1 a2 b2 a b x x₁ eqt2 ,
                eqInType-⇛-QLT u w A B a1 b1 a2 b2 a b x x₁ eqt2

eqInType-ext0 {u} isu {w} {A} {B} (EQTFREE x x₁) ind =
  λ eqt2 a b → eqInType-⇛-FREE-rev u w A B a b x x₁ eqt2 ,
                eqInType-⇛-FREE u w A B a b x x₁ eqt2

eqInType-ext0 {u} isu {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind =
  λ eqt2 a b → eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2 ,
                eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypePIa u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1))

    indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a₁ a₂ eqa = ind (eqtb w1 e1 a₁ a₂ eqa) (<Type1 _ _ (<TypePIb u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1 a₁ a₂ eqa))

eqInType-ext0 {u} isu {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind =
  λ eqt2 a b → eqInType-⇛-SUM-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2 ,
                eqInType-⇛-SUM u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeSUMa u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1))

    indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a₁ a₂ eqa = ind (eqtb w1 e1 a₁ a₂ eqa) (<Type1 _ _ (<TypeSUMb u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1 a₁ a₂ eqa))

eqInType-ext0 {u} isu {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind =
  λ eqt2 a b → eqInType-⇛-SET-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2 ,
                eqInType-⇛-SET u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeSETa u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1))

    indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2) → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a₁ a₂ eqa = ind (eqtb w1 e1 a₁ a₂ eqa) (<Type1 _ _ (<TypeSETb u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1 a₁ a₂ eqa))

eqInType-ext0 {u} isu {w} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2) ind =
  λ eqt2 a b → eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda x x₁ eqt2 ,
                eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeEQ u w A B a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2 w1 e1))

eqInType-ext0 {u} isu {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind =
  λ eqt2 a b → eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2 ,
                eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeUNIONl u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1))

    indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1))
    indb w1 e1 = ind (eqtb w1 e1) (<Type1 _ _ (<TypeUNIONr u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w1 e1))

eqInType-ext0 {u} isu {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqta exta) ind =
  λ eqt2 a b → eqInType-⇛-TSQUASH-rev u w A B A1 A2 a b eqta exta inda x x₁ eqt2 ,
                eqInType-⇛-TSQUASH u w A B A1 A2 a b eqta exta inda x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeSQUASH u w A B A1 A2 x x₁ eqta exta w1 e1))

--eqInType-ext0 {u} isu {w} {A} {B} (EQTDUM A1 A2 x x₁ eqta) ind = {!!}
eqInType-ext0 {u} isu {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) ind =
  λ eqt2 a b → eqInType-⇛-FFDEFS-rev u w A B A1 A2 x1 x2 a b eqta exta inda x x₁ eqt2 ,
                eqInType-⇛-FFDEFS u w A B A1 A2 x1 x2 a b eqta exta inda x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeFFDEFS u w A B A1 A2 x1 x2 x x₁ eqta exta eqx w1 e1))

eqInType-ext0 {u} isu {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqta) ind = ?
{--  λ eqt2 a b → eqInType-⇛-TSQUASH-rev u w A B A1 A2 a b eqta exta inda x x₁ eqt2 ,
                eqInType-⇛-TSQUASH u w A B A1 A2 a b eqta exta inda x x₁ eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    inda w1 e1 = ind (eqta w1 e1) (<Type1 _ _ (<TypeSQUASH w A B A1 A2 x x₁ eqta exta w1 e1))--}

eqInType-ext0 {u} (n , isu) {w} {A} {B} (EQTUNIV m p c₁ c₂) ind rewrite isu = eqInTypeExt-EQTUNIV m p c₁ c₂
eqInType-ext0 {u} isu {w} {A} {B} (EQTBAR x) ind =
  λ eqt' a b → (λ ei → eqInType-ext-bar {u} isu x ind a b ei eqt') ,
                (λ ei → eqInType-ext-bar-rev {u} isu x ind a b eqt' ei)



eqInType-ext : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm} (eqt : eqTypes u w A B) → eqInTypeExt eqt
eqInType-ext {u} isu {w} {A} {B} eqt = ind<Type eqInTypeExt (eqInType-ext0 isu) eqt




is-uni→eqTypes : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
                  (eqt : eqTypes u w A B)
                  → eqTypes (uni (fst isu)) w A B
is-uni→eqTypes {u} (n , isu) {w} {A} {B} eqt rewrite isu = eqt




is-uni→eqInType : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm} {a b : CTerm}
                   (eqt : eqTypes u w A B)
                   (eqi : eqInType u w eqt a b)
                   → Σ (eqTypes (uni (fst isu)) w A B) (λ z → eqInType (uni (fst isu)) w z a b)
is-uni→eqInType {u} (n , isu) {w} {A} {B} {a} {b} eqt eqi rewrite isu = eqt , eqi




is-uni-eqInType→ : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm} {a b : CTerm}
                    (eqt : eqTypes (uni (fst isu)) w A B)
                    (eqi : eqInType (uni (fst isu)) w eqt a b)
                    (eqt' : eqTypes u w A B)
                    → eqInType u w eqt' a b
is-uni-eqInType→ {u} (n , isu) {w} {A} {B} {a} {b} eqt eqi eqt' rewrite isu =
  fst (eqInType-ext {uni n} (is-uni-uni n) eqt eqt' a b) eqi





wPredDepExtIrr-eqInType-if-inbar : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B a b : CTerm}
                                   (x : inbar w (λ w' _ → eqTypes u w' A B))
                                   → wpreddepextirr (λ w1 e1 z → eqInType u w1 z a b) x
wPredDepExtIrr-eqInType-if-inbar {u} isu {w} {A} {B} {a} {b} x w0 w1 w2 e0 e1 e2 e0' e1' e2' q =
  fst (eqInType-ext {u} isu {w2} {A} {B} (snd (snd (x w0 e0)) w2 e0' e2') (snd (snd (x w1 e1)) w2 e1' e2) a b) q




local-eqInType : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                 → (i : inbar w (λ w' e → eqTypes u w' A B))
                 → inbar' w i (λ w' e z → eqInType u w' z a b)
                 → Σ (eqTypes u w A B) (λ eqt → eqInType u w eqt a b)
local-eqInType u w A B a b i j = EQTBAR i , j




local-eqInType2 : (u : univs) (isu : is-uni u) (w : 𝕎·) (A B a b : CTerm)
                  → (eqt : eqTypes u w A B)
                  → (i : inbar w (λ w' e → eqTypes u w' A B))
                  → inbar' w i (λ w' e z → eqInType u w' z a b)
                  → eqInType u w eqt a b
{-# TERMINATING #-}
local-eqInType2 u isu w A B a b (EQTNAT x x₁) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w1 e1 → w ⊑· w1 → #strongMonEq w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 s x → s) h1
      where
        h1 : eqInType u w' {A} {B} (EQTNAT (⇛-mon e' x) (⇛-mon e' x₁)) a b
        h1 = fst (eqInType-ext isu z (EQTNAT (⇛-mon e' x) (⇛-mon e' x₁)) a b) ei

local-eqInType2 u isu w A B a b (EQTQNAT x x₁) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w1 e1 → w ⊑· w1 → #weakMonEq w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 s x → s) h1
      where
        h1 : eqInType u w' {A} {B} (EQTQNAT (⇛-mon e' x) (⇛-mon e' x₁)) a b
        h1 = fst (eqInType-ext isu z (EQTQNAT (⇛-mon e' x) (⇛-mon e' x₁)) a b) ei

local-eqInType2 u isu w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w1 e1 → w ⊑· w1 → #lift-<NUM-pair w1 a1 b1))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 s x → s) h1
      where
        h1 : eqInType u w' {A} {B} (EQTLT a1 a2 b1 b2 (⇛-mon e' x) (⇛-mon e' x₁) (#strongMonEq-mon {a1} {a2} x₂ w' e') (#strongMonEq-mon {b1} {b2} x₃ w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTLT a1 a2 b1 b2 (⇛-mon e' x) (⇛-mon e' x₁) (#strongMonEq-mon {a1} {a2} x₂ w' e') (#strongMonEq-mon {b1} {b2} x₃ w' e')) a b) ei

local-eqInType2 u isu w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w1 e1 → w ⊑· w1 → #lift-<NUM-pair w1 a1 b1))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 s x → s) h1
      where
        h1 : eqInType u w' {A} {B} (EQTQLT a1 a2 b1 b2 (⇛-mon e' x) (⇛-mon e' x₁) (#weakMonEq-mon {a1} {a2} x₂ w' e') (#weakMonEq-mon {b1} {b2} x₃ w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTQLT a1 a2 b1 b2 (⇛-mon e' x) (⇛-mon e' x₁) (#weakMonEq-mon {a1} {a2} x₂ w' e') (#weakMonEq-mon {b1} {b2} x₃ w' e')) a b) ei

local-eqInType2 u isu w A B a b (EQTFREE x x₁) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w1 e1 → w ⊑· w1 → #⇛to-same-CS w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 s x → s) h1
      where
        h1 : eqInType u w' {A} {B} (EQTFREE (⇛-mon e' x) (⇛-mon e' x₁)) a b
        h1 = fst (eqInType-ext isu z (EQTFREE (⇛-mon e' x) (⇛-mon e' x₁)) a b) ei

local-eqInType2 u isu w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → PIeq (eqInType u w1 (eqta w1 x)) (λ a1 a2 eqa → eqInType u w1 (eqtb w1 x a1 a2 eqa)) a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTPI A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTPI A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → PIeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ b₁ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ b₁ eqa)) a b
                                 → (x₂ : w ⊑· w'') → PIeq (eqInType u w'' (eqta w'' x₂)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x₂ a1 a2 eqa)) a b)
        aw' w1 e1 h x₂ = PIeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {a} {b} exta extb h

local-eqInType2 u isu w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → SUMeq (eqInType u w1 (eqta w1 x)) (λ a1 a2 eqa → eqInType u w1 (eqtb w1 x a1 a2 eqa)) w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → SUMeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ b₁ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ b₁ eqa)) w'' a b
                                 → (x₂ : w ⊑· w'') → SUMeq (eqInType u w'' (eqta w'' x₂)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x₂ a1 a2 eqa)) w'' a b)
        aw' w1 e1 h x₂ = SUMeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

local-eqInType2 u isu w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → SETeq (eqInType u w1 (eqta w1 x)) (λ a1 a2 eqa → eqInType u w1 (eqtb w1 x a1 a2 eqa)) a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → SETeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ b₁ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ b₁ eqa)) a b
                                 → (x₂ : w ⊑· w'') → SETeq (eqInType u w'' (eqta w'' x₂)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x₂ a1 a2 eqa)) a b)
        aw' w1 e1 h x₂ = SETeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

local-eqInType2 u isu w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta exta eqt1 eqt2) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → EQeq a1 a2 (eqInType u w1 (eqta w1 x)) w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqt1) (∀𝕎-mon e' eqt2)) a b
        h1 = fst (eqInType-ext isu z (EQTEQ a1 b1 a2 b2 A₁ B₁ (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqt1) (∀𝕎-mon e' eqt2)) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → EQeq a1 a2 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → (x₂ : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x₂)) w'' a b)
        aw' w1 e1 h x₂ = EQeq-ext {u} {w} {A₁} {B₁} {a1} {a2} {eqta} {_} {_} {_} {a} {b} exta h

local-eqInType2 u isu w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → UNIONeq (eqInType u w1 (eqta w1 x)) (eqInType u w1 (eqtb w1 x)) w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTUNION A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredExtIrr-eqInType-mon eqtb extb w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTUNION A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredExtIrr-eqInType-mon eqtb extb w' e')) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → UNIONeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (eqInType u w'' (∀𝕎-mon e' eqtb w'' e'')) w'' a b
                                 → (x₂ : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x₂)) (eqInType u w'' (eqtb w'' x₂)) w'' a b)
        aw' w1 e1 h x₂ = UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

local-eqInType2 u isu w A B a b (EQTSQUASH A1 A2 x x₁ eqta exta) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → TSQUASHeq (eqInType u w1 (eqta w1 x)) w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTSQUASH A1 A2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTSQUASH A1 A2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → (x₂ : w ⊑· w'') → TSQUASHeq (eqInType u w'' (eqta w'' x₂)) w'' a b)
        aw' w1 e1 h x₂ = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h

--local-eqInType2 u isu w A B a b (EQTDUM A1 A2 x x₁ eqta) i j = lift tt
local-eqInType2 u isu w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → FFDEFSeq x1 (eqInType u w1 (eqta w1 x)) w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQFFDEFS A1 A2 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqx)) a b
        h1 = fst (eqInType-ext isu z (EQFFDEFS A1 A2 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqx)) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → FFDEFSeq x1 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → (x₂ : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x₂)) w'' a b)
        aw' w1 e1 h x₂ = FFDEFSeq-ext {u} {w} {A1} {A2} {x1} {eqta} {_} {_} {_} {a} {b} exta h

local-eqInType2 u (n , isu) w A B a b (EQTUNIV m p c₁ c₂) i j rewrite isu =
  inbarEqTypes→uniUpTo
    {m} {n} {p} {w} {a} {b}
    (Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j))
    where
      aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) → atbar i w' e' z
                          → eqInType (uni n) w' z a b
                          → inbar w' (↑wPred' (λ w'' e → eqTypes (uni m) w'' a b) e'))
      aw w' e' z at eqi =
        Bar.∀𝕎-inBarFunc inOpenBar-Bar
          (λ w1 e1 et z → et)
          (uniUpTo→inbarEqTypes {m} {n} {p} {w'} {a} {b} (eqInType-u-rev p (⇛-mon e' c₁) (⇛-mon e' c₂) z a b eqi))

local-eqInType2 u isu w A B a b (EQTLIFT A1 A2 x x₁ eqta) i j = ?
{--  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w1 e1 → (x : w ⊑· w1) → TSQUASHeq (eqInType u w1 (eqta w1 x)) w1 a b))
    aw w' e' z at ei = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw' h1
      where
        h1 : eqInType u w' {A} {B} (EQTSQUASH A1 A2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) a b
        h1 = fst (eqInType-ext isu z (EQTSQUASH A1 A2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) a b) ei

        aw' : ∀𝕎 w' (λ w'' e'' → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b
                                 → (x₂ : w ⊑· w'') → TSQUASHeq (eqInType u w'' (eqta w'' x₂)) w'' a b)
        aw' w1 e1 h x₂ = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h--}

local-eqInType2 u isu w A B a b (EQTBAR x) i j =
  Bar.inBar'-change inOpenBar-Bar i x aw j
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ y : eqTypes u w' A B) → atbar i w' e' x₁ → atbar x w' e' y
                         → eqInType u w' x₁ a b
                         → eqInType u w' y a b)
    aw w' e' x₁ x₂ at₁ at₂ eqi = proj₁ (eqInType-ext isu x₁ x₂ a b) eqi





{--
local-eqInType3 : (u : univs) (isu : is-universe u) (w : 𝕎·) (A B a b : CTerm)
                  → (i : inbar w (λ w' e → eqTypes u w' A B))
                  → inbar' w i (λ w' e z → eqInType u w' z a b)
--                  → inbar' w i (λ w' e → TSP)
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b × eqInTypeExt eqt
local-eqInType3 u isu w A B a b i j (EQTNAT x x₁) =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar aw i j) ,
  (λ eqt2 a b → eqInType-⇛-NAT-rev u isu w A B a b x x₁ eqt2 , eqInType-⇛-NAT u isu w A B a b x x₁ eqt2)
  where
    aw : ∀𝕎 w (λ w' e' → (x₂ : eqTypes u w' A B)
                         → eqInType u w' x₂ a b
                         → inbar w' (↑wPred' (λ w'' e → strongMonEq w'' a b) e'))
    aw w' e' x₂ eqt' = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 z k → z) aw'
      where
        aw' : inbar w' (λ w'' _ → strongMonEq w'' a b)
        aw' = eqInType-⇛-NAT u isu w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) x₂ eqt'
local-eqInType3 u isu w A B a b i j (EQTQNAT x x₁) = {!!}
local-eqInType3 u isu w A B a b i j (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
local-eqInType3 u isu w A B a b i j (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
local-eqInType3 u isu w A B a b i j (EQTFREE x x₁) = {!!}
local-eqInType3 u isu w A B a b i j (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = {!!}
local-eqInType3 u isu w A B a b i j (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
local-eqInType3 u isu w A B a b i j (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
local-eqInType3 u isu w A B a b i j (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) = {!!}
local-eqInType3 u isu w A B a b i j (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) = {!!}
local-eqInType3 u isu w A B a b i j (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
local-eqInType3 u isu w A B a b i j (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
local-eqInType3 u isu w A B a b i j (EQTUNIV x) = {!!}
local-eqInType3 u isu w A B a b i j (EQTBAR x) = {!!}
--}


TSP-change : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
             (eqt1 eqt2 : eqTypes u w A B)
             → TSP eqt1
             → TSP eqt2
TSP-change {u} isu {w} {A} {B} eqt1 eqt2 tsp =
  mktsp (TSP.tsym tsp) ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrevl1 iextrevl2 iextrevr1 iextrevr2 local
  where
    ttrans : eqTypesTrans u w A B
    ttrans C eqt = TSP.ttrans tsp C eqt

    isym : eqInTypeSym u eqt2
    isym a b eqi = fst (eqInType-ext isu eqt1 eqt2 b a) (TSP.isym tsp a b (fst (eqInType-ext isu eqt2 eqt1 a b) eqi))

    itrans : eqInTypeTrans u eqt2
    itrans a b c eqi1 eqi2 = proj₁ (eqInType-ext isu eqt1 eqt2 a c) (TSP.itrans tsp a b c (fst (eqInType-ext isu eqt2 eqt1 a b) eqi1) (fst (eqInType-ext isu eqt2 eqt1 b c) eqi2))

    iextl1 : eqInTypeExtL1 eqt2
    iextl1 C eqt' a b eqi = TSP.extl1 tsp C eqt' a b (fst (eqInType-ext isu eqt2 eqt1 a b) eqi)

    iextl2 : eqInTypeExtL2 eqt2
    iextl2 C eqt' a b eqi = TSP.extl2 tsp C eqt' a b (fst (eqInType-ext isu eqt2 eqt1 a b) eqi)

    iextr1 : eqInTypeExtR1 eqt2
    iextr1 C eqt' a b eqi = TSP.extr1 tsp C eqt' a b (fst (eqInType-ext isu eqt2 eqt1 a b) eqi)

    iextr2 : eqInTypeExtR2 eqt2
    iextr2 C eqt' a b eqi = TSP.extr2 tsp C eqt' a b (fst (eqInType-ext isu eqt2 eqt1 a b) eqi)

    iextrevl1 : eqInTypeExtRevL1 eqt2
    iextrevl1 C eqt' a b eqi = fst (eqInType-ext isu eqt1 eqt2 a b) (TSP.extrevl1 tsp C eqt' a b eqi)

    iextrevl2 : eqInTypeExtRevL2 eqt2
    iextrevl2 C eqt' a b eqi = fst (eqInType-ext isu eqt1 eqt2 a b) (TSP.extrevl2 tsp C eqt' a b eqi)

    iextrevr1 : eqInTypeExtRevR1 eqt2
    iextrevr1 C eqt' a b eqi = fst (eqInType-ext isu eqt1 eqt2 a b) (TSP.extrevr1 tsp C eqt' a b eqi)

    iextrevr2 : eqInTypeExtRevR2 eqt2
    iextrevr2 C eqt' a b eqi = fst (eqInType-ext isu eqt1 eqt2 a b) (TSP.extrevr2 tsp C eqt' a b eqi)

    local : eqInTypeLocal eqt2
    local a b i j = proj₁ (eqInType-ext isu eqt1 eqt2 a b) (TSP.local tsp a b i j)




eqInType-mon : {u : univs} (isu : is-uni u) {w : 𝕎·} {A B : CTerm}
               {w' : 𝕎·} (e' : w ⊑· w')
               (eqt1 : eqTypes u w A B)
               (eqt2 : eqTypes u w' A B)
               (a b : CTerm)
               (eqi  : eqInType u w eqt1 a b)
               → eqInType u w' eqt2 a b
{-# TERMINATING #-}
eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTNAT x x₁) eqt2 a b eqi =
  eqInType-⇛-NAT-rev u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) eqt2 ei
  where
    ei : inbar w' (λ w'' e → #strongMonEq w'' a b)
    ei = ↑inbar eqi e'

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTQNAT x x₁) eqt2 a b eqi =
  eqInType-⇛-QNAT-rev u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) eqt2 ei
  where
    ei : inbar w' (λ w'' e → #weakMonEq w'' a b)
    ei = ↑inbar eqi e'

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqt2 a b eqi =
  eqInType-⇛-LT-rev u w' A B a1 b1 a2 b2 a b (⇛-mon e' x) (⇛-mon e' x₁) eqt2 ei
  where
    ei : inbar w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
    ei = ↑inbar eqi e'

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqt2 a b eqi =
  eqInType-⇛-QLT-rev u w' A B a1 b1 a2 b2 a b (⇛-mon e' x) (⇛-mon e' x₁) eqt2 ei
  where
    ei : inbar w' (λ w'' e → #lift-<NUM-pair w'' a1 b1)
    ei = ↑inbar eqi e'

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTFREE x x₁) eqt2 a b eqi =
  eqInType-⇛-FREE-rev u w' A B a b (⇛-mon e' x) (⇛-mon e' x₁) eqt2 ei
  where
    ei : inbar w' (λ w'' e → #⇛to-same-CS w'' a b)
    ei = ↑inbar eqi e'

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqt2 a b eqi =
  eqInType-⇛-PI-rev2
    u w' A B A1 A2 B1 B2 a b
    (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
    (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → PIeq (eqInType u w''' (eqta w''' e)) (λ a₁ a₂ eqa → eqInType u w''' (eqtb w''' e a₁ a₂ eqa)) a b) e' w'' e''
                            → PIeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) a b)
    aw w1 e1 h = PIeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

    ib : inbar w' (λ w'' e → PIeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e a₁ a₂ eqa)) a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqt2 a b eqi =
  eqInType-⇛-SUM-rev2
    u w' A B A1 A2 B1 B2 a b
    (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
    (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → SUMeq (eqInType u w''' (eqta w''' e)) (λ a₁ a₂ eqa → eqInType u w''' (eqtb w''' e a₁ a₂ eqa)) w''' a b) e' w'' e''
                            → SUMeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) w'' a b)
    aw w1 e1 h = SUMeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

    ib : inbar w' (λ w'' e → SUMeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e a₁ a₂ eqa)) w'' a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqt2 a b eqi =
  eqInType-⇛-SET-rev2
    u w' A B A1 A2 B1 B2 a b
    (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
    (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → SETeq (eqInType u w''' (eqta w''' e)) (λ a₁ a₂ eqa → eqInType u w''' (eqtb w''' e a₁ a₂ eqa)) a b) e' w'' e''
                            → SETeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e'' a₁ a₂ eqa)) a b)
    aw w1 e1 h = SETeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} exta extb h

    ib : inbar w' (λ w'' e → SETeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (λ a₁ a₂ eqa → eqInType u w'' (∀𝕎-mon e' eqtb w'' e a₁ a₂ eqa)) a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta exta eqt1 eqt3) eqt2 a b eqi =
  eqInType-⇛-EQ-rev2
    u w' A B A₁ B₁ a1 b1 a2 b2 a b
    (∀𝕎-mon e' eqta)
    (wPredExtIrr-eqInType-mon eqta exta w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → EQeq a1 a2 (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                            → EQeq a1 a2 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
    aw w1 e1 h = EQeq-ext {u} {w} {A₁} {B₁} {a1} {a2} {eqta} {_} {_} {_} {a} {b} exta h

    ib : inbar w' (λ w'' e → EQeq a1 a2 (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqt2 a b eqi =
  eqInType-⇛-UNION-rev2
    u w' A B A1 A2 B1 B2 a b
    (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
    (wPredExtIrr-eqInType-mon eqta exta w' e')
    (wPredExtIrr-eqInType-mon eqtb extb w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → UNIONeq (eqInType u w''' (eqta w''' e)) (eqInType u w''' (eqtb w''' e)) w''' a b) e' w'' e''
                            → UNIONeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) (eqInType u w'' (∀𝕎-mon e' eqtb w'' e'')) w'' a b)
    aw w1 e1 h = UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {_} {_} {_} {a} {b} exta extb h

    ib : inbar w' (λ w'' e → UNIONeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) (eqInType u w'' (∀𝕎-mon e' eqtb w'' e)) w'' a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTSQUASH A1 A2 x x₁ eqta exta) eqt2 a b eqi =
  eqInType-⇛-TSQUASH-rev2
    u w' A B A1 A2 a b
    (∀𝕎-mon e' eqta)
    (wPredExtIrr-eqInType-mon eqta exta w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → TSQUASHeq (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                            → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
    aw w1 e1 h = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h

    ib : inbar w' (λ w'' e → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

--eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTDUM A1 A2 x x₁ eqta) eqt2 a b eqi = {!!}
eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) eqt2 a b eqi =
  eqInType-⇛-FFDEFS-rev2
    u w' A B A1 A2 x1 x2 a b
    (∀𝕎-mon e' eqta)
    (wPredExtIrr-eqInType-mon eqta exta w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → FFDEFSeq x1 (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                            → FFDEFSeq x1 (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
    aw w1 e1 h = FFDEFSeq-ext {u} {w} {A1} {A2} {x1} {eqta} {_} {_} {_} {a} {b} exta h

    ib : inbar w' (λ w'' e → FFDEFSeq x1 (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')

eqInType-mon {u} (n , isu) {w} {A} {B} {w'} e' (EQTUNIV m p c₁ c₂) eqt2 a b eqi rewrite isu =
  eqInType-u p (⇛-mon e' c₁) (⇛-mon e' c₂) eqt2 a b (uniUpTo-mon {n} {m} {p} eqi w' e')

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTLIFT A1 A2 x x₁ eqta) eqt2 a b eqi = ?
{--  eqInType-⇛-TSQUASH-rev2
    u w' A B A1 A2 a b
    (∀𝕎-mon e' eqta)
    (wPredExtIrr-eqInType-mon eqta exta w' e')
    (⇛-mon e' x) (⇛-mon e' x₁) eqt2 (λ eqt' lety → eqInType-ext isu eqt') ib
  where
    aw : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → TSQUASHeq (eqInType u w''' (eqta w''' e)) w''' a b) e' w'' e''
                            → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e'')) w'' a b)
    aw w1 e1 h = TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {_} {_} {_} {a} {b} exta h

    ib : inbar w' (λ w'' e → TSQUASHeq (eqInType u w'' (∀𝕎-mon e' eqta w'' e)) w'' a b)
    ib = Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (↑inbar eqi e')--}

eqInType-mon {u} isu {w} {A} {B} {w'} e' (EQTBAR x) eqt2 a b eqi =
  local-eqInType2 u isu w' A B a b eqt2 ib ib'
  where
    ib : inbar w' (λ w'' e → eqTypes u w'' A B)
    ib = ↑inbar x e'

    aw : ∀𝕎 w (λ w'' e'' → (x₁ y : eqTypes u w'' A B) (at₁ : atbar x w'' e'' x₁) (at₂ : atbar x w'' e'' y)
                           → eqInType u w'' x₁ a b
                           → (w' : 𝕎·) (e' : w'' ⊑· w') (eqt2 : eqTypes u w' A B) → eqInType u w' eqt2 a b)
    aw w'' e'' x₁ y at₁ at₂ eqi' w''' e''' eqt2' = eqInType-mon isu e''' x₁ eqt2' a b eqi'

    ind : inbar' w x (λ w1 e1 z → (w' : 𝕎·) (e' : w1 ⊑· w') (eqt2 : eqTypes u w' A B) → eqInType u w' eqt2 a b)
    ind = Bar.inBar'-change inOpenBar-Bar x x aw eqi

    aw' : ∀𝕎 w (λ w'' e'' → (x₁ y : eqTypes u w'' A B) (at₁ : atbar x w'' e'' x₁) (at₂ : atbar x w'' e'' y)
                            → ((w' : 𝕎·) (e' : w'' ⊑· w') (eqt2 : eqTypes u w' A B) → eqInType u w' eqt2 a b)
                            → eqInType u w'' y a b)
    aw' w'' e'' x₁ y at₁ at₂ imp = imp w'' (⊑-refl· w'') y

    ib0 : inbar' w x (λ w'' e z → eqInType u w'' z a b)
    ib0 = Bar.inBar'-change inOpenBar-Bar x x aw' ind

    ib1 : inbar' w' ib (↑wPredDep (λ w'' e (z : eqTypes u w'' A B) → eqInType u w'' z a b) e')
    ib1 = ↑inbar' {w} {λ w e → eqTypes u w A B} {λ w e z → eqInType u w z a b} x e' ib0

    ib' : inbar' w' ib (λ w'' e z → eqInType u w'' z a b)
    ib' = ib1




typeSysConds-BAR : (u : univs) (isu : is-uni u) (w : 𝕎·) (A B : CTerm)
                   (x : inbar w (λ w' _ → eqTypes u w' A B))
                   (ind : inbar' w x (λ w1 e1 z → TSP z))
                   → TSP (EQTBAR x)
typeSysConds-BAR u isu w A B x ind =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrevl1 iextrevl2 iextrevr1 iextrevr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTBAR (Bar.∀𝕎-inBar'-inBar inOpenBar-Bar x aw ind)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → TSP z → eqTypes u w' B A)
        aw w1 e1 eqt at tsp = TSP.tsym tsp

    ttrans : eqTypesTrans u w A B
    ttrans C eqt = typeSysConds-BAR-ttrans u w A B C x ind eqt

    isym : eqInTypeSym u (EQTBAR x)
    isym a b eqi = Bar.inBar'-comb inOpenBar-Bar x aw ind eqi
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B) → TSP zg → eqInType u w' zh a b → eqInType u w' z b a)
        aw w1 e1 z zg zh tsp i = TSP.extl1 tsp B z b a (TSP.extrevl1 tsp B zg b a (TSP.isym tsp a b (TSP.extrevl1 tsp B zh a b i)))

    itrans : eqInTypeTrans u (EQTBAR x)
    itrans a b c eqi₁ eqi₂ = inBar'3 inOpenBar-Bar x aw ind eqi₁ eqi₂
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh zk : eqTypes u w' A B) → TSP zg → eqInType u w' zh a b → eqInType u w' zk b c → eqInType u w' z a c)
        aw w1 e1 z zg zh zk tsp i j = TSP.extl1 tsp B z a c (TSP.itrans tsp a b c i1 i2)
          where
            i1 : eqInType u w1 zg a b
            i1 = TSP.extrevl1 tsp B zh a b i

            i2 : eqInType u w1 zg b c
            i2 = TSP.extrevl1 tsp B zk b c j

    iextl1 : eqInTypeExtL1 (EQTBAR x)
    iextl1 C eqt a b eqi = local-eqInType2 u isu w A C a b eqt j ei'
      where
        j : inbar w (λ w' e → eqTypes u w' A C)
        j = Bar.∀𝕎-inBar inOpenBar-Bar (eqTypes-mon u eqt)

        aw : ∀𝕎 w (λ w' e' → (x₁ : eqTypes u w' A B) (x₂ : eqTypes u w' A C) (at₁ : atbar x w' e' x₁) (at₂ : atbar j w' e' x₂)
                             → TSP x₁ × eqInType u w' x₁ a b
                             → eqInType u w' x₂ a b)
        aw w' e' x₁ x₂ at₁ at₂ (tsp , eqi) = TSP.extl1 tsp C x₂ a b eqi

        aw' : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                              → TSP zg → eqInType u w' zh a b → TSP z × eqInType u w' z a b)
        aw' w' e' z zg zh tsp eqi = TSP-change isu zg z tsp , fst (eqInType-ext isu zh z a b) eqi

        ei' : inbar' w j (λ w' e z → eqInType u w' z a b)
        ei' = Bar.inBar'-change inOpenBar-Bar x j aw (Bar.inBar'-comb inOpenBar-Bar x aw' ind eqi)

    iextl2 : eqInTypeExtL2 (EQTBAR x)
    iextl2 C eqt a b eqi = local-eqInType2 u isu w C A a b eqt j ei'
      where
        j : inbar w (λ w' e → eqTypes u w' C A)
        j = Bar.∀𝕎-inBar inOpenBar-Bar (eqTypes-mon u eqt)

        aw : ∀𝕎 w (λ w' e' → (x₁ : eqTypes u w' A B) (x₂ : eqTypes u w' C A) (at₁ : atbar x w' e' x₁) (at₂ : atbar j w' e' x₂)
                             → TSP x₁ × eqInType u w' x₁ a b
                             → eqInType u w' x₂ a b)
        aw w' e' x₁ x₂ at₁ at₂ (tsp , eqi) = TSP.extl2 tsp C x₂ a b eqi

        aw' : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                              → TSP zg → eqInType u w' zh a b → TSP z × eqInType u w' z a b)
        aw' w' e' z zg zh tsp eqi = TSP-change isu zg z tsp , fst (eqInType-ext isu zh z a b) eqi

        ei' : inbar' w j (λ w' e z → eqInType u w' z a b)
        ei' = Bar.inBar'-change inOpenBar-Bar x j aw (Bar.inBar'-comb inOpenBar-Bar x aw' ind eqi)

    iextr1 : eqInTypeExtR1 (EQTBAR x)
    iextr1 C eqt a b eqi = local-eqInType2 u isu w C B a b eqt j ei'
      where
        j : inbar w (λ w' e → eqTypes u w' C B)
        j = Bar.∀𝕎-inBar inOpenBar-Bar (eqTypes-mon u eqt)

        aw : ∀𝕎 w (λ w' e' → (x₁ : eqTypes u w' A B) (x₂ : eqTypes u w' C B) (at₁ : atbar x w' e' x₁) (at₂ : atbar j w' e' x₂)
                             → TSP x₁ × eqInType u w' x₁ a b
                             → eqInType u w' x₂ a b)
        aw w' e' x₁ x₂ at₁ at₂ (tsp , eqi) = TSP.extr1 tsp C x₂ a b eqi

        aw' : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                              → TSP zg → eqInType u w' zh a b → TSP z × eqInType u w' z a b)
        aw' w' e' z zg zh tsp eqi = TSP-change isu zg z tsp , fst (eqInType-ext isu zh z a b) eqi

        ei' : inbar' w j (λ w' e z → eqInType u w' z a b)
        ei' = Bar.inBar'-change inOpenBar-Bar x j aw (Bar.inBar'-comb inOpenBar-Bar x aw' ind eqi)

    iextr2 : eqInTypeExtR2 (EQTBAR x)
    iextr2 C eqt a b eqi = local-eqInType2 u isu w B C a b eqt j ei'
      where
        j : inbar w (λ w' e → eqTypes u w' B C)
        j = Bar.∀𝕎-inBar inOpenBar-Bar (eqTypes-mon u eqt)

        aw : ∀𝕎 w (λ w' e' → (x₁ : eqTypes u w' A B) (x₂ : eqTypes u w' B C) (at₁ : atbar x w' e' x₁) (at₂ : atbar j w' e' x₂)
                             → TSP x₁ × eqInType u w' x₁ a b
                             → eqInType u w' x₂ a b)
        aw w' e' x₁ x₂ at₁ at₂ (tsp , eqi) = TSP.extr2 tsp C x₂ a b eqi

        aw' : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                              → TSP zg → eqInType u w' zh a b → TSP z × eqInType u w' z a b)
        aw' w' e' z zg zh tsp eqi = TSP-change isu zg z tsp , fst (eqInType-ext isu zh z a b) eqi

        ei' : inbar' w j (λ w' e z → eqInType u w' z a b)
        ei' = Bar.inBar'-change inOpenBar-Bar x j aw (Bar.inBar'-comb inOpenBar-Bar x aw' ind eqi)

    iextrevl1 : eqInTypeExtRevL1 (EQTBAR x)
    iextrevl1 C eqt a b eqi = Bar.inBar'-comb inOpenBar-Bar x aw ind ind
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                             → TSP zg → TSP zh → eqInType u w' z a b)
        aw w' e' z zg zh tsp _ =
          TSP.extl1
            tsp B z a b
            (TSP.extrevl1
              tsp C
              (eqTypes-mon u eqt w' e')
              a b
              (eqInType-mon isu e' eqt (eqTypes-mon u eqt w' e') a b eqi))

    iextrevl2 : eqInTypeExtRevL2 (EQTBAR x)
    iextrevl2 C eqt a b eqi = Bar.inBar'-comb inOpenBar-Bar x aw ind ind
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                             → TSP zg → TSP zh → eqInType u w' z a b)
        aw w' e' z zg zh tsp _ =
          TSP.extl1 tsp B z a b
            (TSP.extrevl2
                tsp C (eqTypes-mon u eqt w' e') a b
                (eqInType-mon isu e' eqt (eqTypes-mon u eqt w' e') a b eqi))

    iextrevr1 : eqInTypeExtRevR1 (EQTBAR x)
    iextrevr1 C eqt a b eqi = Bar.inBar'-comb inOpenBar-Bar x aw ind ind
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                             → TSP zg → TSP zh → eqInType u w' z a b)
        aw w' e' z zg zh tsp _ =
          TSP.extl1 tsp B z a b
            (TSP.extrevr1
                tsp C (eqTypes-mon u eqt w' e') a b
                (eqInType-mon isu e' eqt (eqTypes-mon u eqt w' e') a b eqi))

    iextrevr2 : eqInTypeExtRevR2 (EQTBAR x)
    iextrevr2 C eqt a b eqi = Bar.inBar'-comb inOpenBar-Bar x aw ind ind
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                             → TSP zg → TSP zh → eqInType u w' z a b)
        aw w' e' z zg zh tsp _ =
          TSP.extl1 tsp B z a b
            (TSP.extrevr2
                tsp C (eqTypes-mon u eqt w' e') a b
                (eqInType-mon isu e' eqt (eqTypes-mon u eqt w' e') a b eqi))

    local : eqInTypeLocal (EQTBAR x)
    local a b i j = Bar.inBar'-comb inOpenBar-Bar x aw ind ind
      where
        aw : ∀𝕎 w (λ w' e' → (z zg zh : eqTypes u w' A B)
                             → TSP zg → TSP zh → eqInType u w' z a b)
        aw w' e' z zg zh tsp _ =
          TSP.extl1 tsp B z a b
            (TSP.local tsp a b (↑inbar i e') ib)
          where
            ib : inbar' w' (↑inbar i e') (↑wPredDep (λ w'' e (z₁ : eqTypes u w'' A B) → eqInType u w'' z₁ a b) e')
            ib = ↑inbar' {w} {λ w e → eqTypes u w A B} {λ w e z → eqInType u w z a b} i e' j





eqUnivi-sym : {n : ℕ} {w : 𝕎·} {A B : CTerm} → eqUnivi n w A B → eqUnivi n w B A
eqUnivi-sym {n} {w} {A} {B} h = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 (c₁ , c₂) → c₂ , c₁) h



eqUnivi-trans : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B C : CTerm}
                → A #⇛ #UNIV i at w
                → B #⇛ #UNIV i at w
                → eqTypes (uni n) w B C
                → eqTypes (uni n) w A C
{-# TERMINATING #-}
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTNAT x x₁) = ⊥-elim (UNIVneqNAT (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTQNAT x x₁) = ⊥-elim (UNIVneqQNAT (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (UNIVneqLT (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (UNIVneqQLT (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTFREE x x₁) = ⊥-elim (UNIVneqFREE (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (UNIVneqPI (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (UNIVneqSUM (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (UNIVneqSET (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) = ⊥-elim (UNIVneqEQ (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) = ⊥-elim (UNIVneqUNION (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqta exta) = ⊥-elim (UNIVneqTSQUASH (⇛-val-det tt tt c₂ x))
--eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTDUM A1 A2 x x₁ eqta) = ⊥-elim (UNIVneqDUM (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) = ⊥-elim (UNIVneqFFDEFS (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTUNIV m q d₁ d₂) =
  EQTUNIV i p c₁ c
  where
    c : C #⇛ #UNIV i at w
    c rewrite UNIVinj (⇛-val-det tt tt d₁ c₂) = d₂
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTLIFT A1 A2 x x₁ eqta) = ⊥-elim (UNIVneqLIFT (⇛-val-det tt tt c₂ x))
eqUnivi-trans {i} {n} p {w} {A} {B} {C} c₁ c₂ (EQTBAR x) =
  EQTBAR (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw x)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes (uni n) w' B C → eqTypes (uni n) w' A C)
    aw w1 e1 eqt =
      eqUnivi-trans p (⇛-mon e1 c₁) (⇛-mon e1 c₂) eqt




eqInUnivi-sym : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
                (ind : (m : ℕ) → m < n → is-TSP-univs (uni m))
                → uniUpTo n i p w A B → uniUpTo n i p w B A
eqInUnivi-sym {i} {n} p {w} {A} {B} ind x =
  inbarEqTypes→uniUpTo {i} {n} {p} {w} {B} {A} (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (uniUpTo→inbarEqTypes {i} {n} {p} x))
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes (uni i) w' A B
                        → eqTypes (uni i) w' B A)
    aw w' e' eqt = TSP.tsym (ind i p w' A B eqt)





eqInUnivi-trans : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B C : CTerm}
                  (ind : (m : ℕ) → m < n → is-TSP-univs (uni m))
                  → uniUpTo n i p w A B
                  → uniUpTo n i p w B C
                  → uniUpTo n i p w A C
eqInUnivi-trans {i} {n} p {w} {A} {B} {C} ind eqi eqj =
  inbarEqTypes→uniUpTo {i} {n} {p} {w} {A} {C}
    (Bar.inBarFunc inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (uniUpTo→inbarEqTypes {i} {n} {p} eqi))
                                 (uniUpTo→inbarEqTypes {i} {n} {p} eqj))
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes (uni i) w' A B
                        → eqTypes (uni i) w' B C
                        → eqTypes (uni i) w' A C)
    aw w' e' eqt1 eqt2 = TSP.ttrans (ind i p w' A B eqt1) C eqt2




eqTypes-preserves-in-bar-⇛-UNIV : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
                                   (eqt : eqTypes (uni n) w A B)
                                   → A B#⇛ #UNIV i at w
                                   → B B#⇛ #UNIV i at w
{-# TERMINATING #-}
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTNAT x x₁) j = ⊥-elim (UNIVneqNAT (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTQNAT x x₁) j = ⊥-elim (UNIVneqQNAT (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) j = ⊥-elim (UNIVneqLT (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) j = ⊥-elim (UNIVneqQLT (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTFREE x x₁) j = ⊥-elim (UNIVneqFREE (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) j = ⊥-elim (UNIVneqPI (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) j = ⊥-elim (UNIVneqSUM (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) j = ⊥-elim (UNIVneqSET (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) j = ⊥-elim (UNIVneqEQ (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) j = ⊥-elim (UNIVneqUNION (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA exta) j = ⊥-elim (UNIVneqTSQUASH (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) j = ⊥-elim (UNIVneqFFDEFS (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTUNIV m q c₁ c₂) j rewrite UNIVinj (Bₗ⇛-val-det tt tt j c₁) = #⇛→B#⇛ {B} {#UNIV m} c₂
--  Bar.inBarFunc inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' (a , b) c → b) x) i
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA) j = ⊥-elim (UNIVneqLIFT (Bₗ⇛-val-det tt tt j x))
eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p {w} {A} {B} (EQTBAR x) j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw x)
  where
    aw0 : ∀𝕎 w (λ w' e' → eqTypes (uni n) w' A B → inbar w' (λ w'' _ → B #⇛ #UNIV i at w''))
    aw0 w' e' eqt = eqTypes-preserves-in-bar-⇛-UNIV {i} {n} p eqt (Bar.↑inBar inOpenBar-Bar j e')

    aw : ∀𝕎 w (λ w' e' → eqTypes (uni n) w' A B → inbar w' (λ w'' _ → (z : w ⊑· w'') → B #⇛ #UNIV i at w''))
    aw w' e' eqt = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' b z → b) (aw0 w' e' eqt)




eqTypes-preserves-in-bar-⇛-UNIV-rev : {i n : ℕ} (p : i < n) {w : 𝕎·} {A B : CTerm}
                                       (eqt : eqTypes (uni n) w A B)
                                       → B B#⇛ #UNIV i at w
                                       → A B#⇛ #UNIV i at w
{-# TERMINATING #-}
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTNAT x x₁) j = ⊥-elim (UNIVneqNAT (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTQNAT x x₁) j = ⊥-elim (UNIVneqQNAT (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) j = ⊥-elim (UNIVneqLT (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) j = ⊥-elim (UNIVneqQLT (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTFREE x x₁) j = ⊥-elim (UNIVneqFREE (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) j = ⊥-elim (UNIVneqPI (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) j = ⊥-elim (UNIVneqSUM (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) j = ⊥-elim (UNIVneqSET (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) j = ⊥-elim (UNIVneqEQ (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) j = ⊥-elim (UNIVneqUNION (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA exta) j = ⊥-elim (UNIVneqTSQUASH (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) j = ⊥-elim (UNIVneqFFDEFS (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTUNIV m q c₁ c₂) j rewrite UNIVinj (Bₗ⇛-val-det tt tt j c₂) = #⇛→B#⇛ {A} {#UNIV m} c₁
--  Bar.inBarFunc inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' (a , b) c → a) x) i
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA) j = ⊥-elim (UNIVneqLIFT (Bₗ⇛-val-det tt tt j x₁))
eqTypes-preserves-in-bar-⇛-UNIV-rev {i} {n} p {w} {A} {B} (EQTBAR x) j =
  Bar.inBar-idem inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw x)
  where
    aw0 : ∀𝕎 w (λ w' e' → eqTypes (uni n) w' A B → inbar w' (λ w'' _ → A #⇛ #UNIV i at w''))
    aw0 w' e' eqt = eqTypes-preserves-in-bar-⇛-UNIV-rev p eqt (Bar.↑inBar inOpenBar-Bar j e')

    aw : ∀𝕎 w (λ w' e' → eqTypes (uni n) w' A B → inbar w' (λ w'' _ → (z : w ⊑· w'') → A #⇛ #UNIV i at w''))
    aw w' e' eqt = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' b z → b) (aw0 w' e' eqt)



is-TSP-univs-eqUnivi : (n : ℕ)
                       (ind : (m : ℕ) → m < n → is-TSP-univs (uni m))
                       (w : 𝕎·) (A B : CTerm)
                       (i : ℕ) (p : i < n)
                       (c₁ : A #⇛ #UNIV i at w)
                       (c₂ : B #⇛ #UNIV i at w)
                       → TSP {uni n} {w} {A} {B} (EQTUNIV i p c₁ c₂)
is-TSP-univs-eqUnivi n ind w A B i p c₁ c₂ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrevl1 iextrevl2 iextrevr1 iextrevr2 local
  where
    tsym : eqTypes (uni n) w B A
    tsym = EQTUNIV i p c₂ c₁

    ttrans : eqTypesTrans (uni n) w A B
    ttrans C h = eqUnivi-trans p c₁ c₂ h

    isym : eqInTypeSym (uni n) {_} {A} {B} (EQTUNIV i p c₁ c₂)
    isym a b eqi = eqInUnivi-sym {i} {n} p {w} {a} {b} ind eqi

    itrans : eqInTypeTrans (uni n) {_} {A} {B} (EQTUNIV i p c₁ c₂)
    itrans a b c eqi₁ eqi₂ = eqInUnivi-trans {i} {n} p {w} {a} {b} {c} ind eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextl1 C eqt' a b eqi =
      eqInType-u-bar {i} {n} p (#⇛→B#⇛ {A} {#UNIV i} c₁)
                               (eqTypes-preserves-in-bar-⇛-UNIV p eqt' (#⇛→B#⇛ {A} {#UNIV i} c₁))
                               eqt' a b eqi

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextl2 C eqt' a b eqi =
      eqInType-u-bar {i} {n} p (eqTypes-preserves-in-bar-⇛-UNIV-rev p eqt' (#⇛→B#⇛ {A} {#UNIV i} c₁))
                               (#⇛→B#⇛ {A} {#UNIV i} c₁)
                               eqt' a b eqi

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextr1 C eqt' a b eqi =
      eqInType-u-bar {i} {n} p (eqTypes-preserves-in-bar-⇛-UNIV-rev p eqt' (#⇛→B#⇛ {B} {#UNIV i} c₂))
                               (#⇛→B#⇛ {B} {#UNIV i} c₂)
                               eqt' a b eqi

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextr2 C eqt' a b eqi =
      eqInType-u-bar {i} {n} p (#⇛→B#⇛ {B} {#UNIV i} c₂)
                               (eqTypes-preserves-in-bar-⇛-UNIV p eqt' (#⇛→B#⇛ {B} {#UNIV i} c₂))
                               eqt' a b eqi

    iextrevl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextrevl1 C eqt' a b eqi =
      eqInType-u-rev-bar {i} {n} p (#⇛→B#⇛ {A} {#UNIV i} c₁)
                                   (eqTypes-preserves-in-bar-⇛-UNIV p eqt' (#⇛→B#⇛ {A} {#UNIV i} c₁))
                                   eqt' a b eqi

    iextrevl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextrevl2 C eqt' a b eqi =
      eqInType-u-rev-bar {i} {n} p (eqTypes-preserves-in-bar-⇛-UNIV-rev p eqt' (#⇛→B#⇛ {A} {#UNIV i} c₁))
                                   (#⇛→B#⇛ {A} {#UNIV i} c₁)
                                   eqt' a b eqi

    iextrevr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextrevr1 C eqt' a b eqi =
      eqInType-u-rev-bar {i} {n} p (eqTypes-preserves-in-bar-⇛-UNIV-rev p eqt' (#⇛→B#⇛ {B} {#UNIV i} c₂))
                                   (#⇛→B#⇛ {B} {#UNIV i} c₂)
                                   eqt' a b eqi

    iextrevr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTUNIV i p c₁ c₂)
    iextrevr2 C eqt' a b eqi =
      eqInType-u-rev-bar {i} {n} p (#⇛→B#⇛ {B} {#UNIV i} c₂)
                                   (eqTypes-preserves-in-bar-⇛-UNIV p eqt' (#⇛→B#⇛ {B} {#UNIV i} c₂))
                                   eqt' a b eqi

    local : eqInTypeLocal (EQTUNIV i p c₁ c₂)
    local a b m j =
      eqInType-u-rev-bar {i} {n} p (#⇛→B#⇛ {A} {#UNIV i} c₁)
                                   (#⇛→B#⇛ {B} {#UNIV i} c₂)
                                   (EQTBAR m) a b
                                   (local-eqInType2 (uni n) (is-uni-uni n) w A B a b (EQTBAR m) m j)



typeSysConds-aux : (n : ℕ) (ind : (m : ℕ) → m < n → is-TSP-univs (uni m))
                   (w : 𝕎·) (A B : CTerm) (eqt : eqTypes (uni n) w A B) → TSP eqt
{-# TERMINATING #-}
typeSysConds-aux n ind w A B (EQTNAT x x₁) = typeSysConds-NAT (uni n) w A B x x₁
typeSysConds-aux n ind w A B (EQTQNAT x x₁) = typeSysConds-QNAT (uni n) w A B x x₁
typeSysConds-aux n ind w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = typeSysConds-LT (uni n) w A B a1 b1 a2 b2 x x₁ x₂ x₃
typeSysConds-aux n ind w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = typeSysConds-QLT (uni n) w A B a1 b1 a2 b2 x x₁ x₂ x₃
typeSysConds-aux n ind w A B (EQTFREE x x₁) = typeSysConds-FREE (uni n) w A B x x₁
typeSysConds-aux n ind w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  typeSysConds-PI (uni n) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqta w1 e1)

    indb : ∀𝕎 w (λ w1 e1 →
                     (a1 a2 : CTerm) (ea : eqInType (uni n) w1 (eqta w1 e1) a1 a2)
                     → TSP (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a1 a2 ea = typeSysConds-aux n ind w1 (sub0 a1 B1) (sub0 a2 B2) (eqtb w1 e1 a1 a2 ea)

typeSysConds-aux n ind w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  typeSysConds-SUM (uni n) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqta w1 e1)

    indb : ∀𝕎 w (λ w1 e1 →
                     (a1 a2 : CTerm) (ea : eqInType (uni n) w1 (eqta w1 e1) a1 a2)
                     → TSP (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a1 a2 ea = typeSysConds-aux n ind w1 (sub0 a1 B1) (sub0 a2 B2) (eqtb w1 e1 a1 a2 ea)

typeSysConds-aux n ind w A B (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  typeSysConds-SET (uni n) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqta w1 e1)

    indb : ∀𝕎 w (λ w1 e1 →
                     (a1 a2 : CTerm) (ea : eqInType (uni n) w1 (eqta w1 e1) a1 a2)
                     → TSP (eqtb w1 e1 a1 a2 ea))
    indb w1 e1 a1 a2 ea = typeSysConds-aux n ind w1 (sub0 a1 B1) (sub0 a2 B2) (eqtb w1 e1 a1 a2 ea)

typeSysConds-aux n ind w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) =
  typeSysConds-EQ (uni n) w A B A₁ B₁ a1 b1 a2 b2 x x₁ eqtA extA inda eqt1 eqt2
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqtA w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A₁ B₁ (eqtA w1 e1)

typeSysConds-aux n ind w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) =
  typeSysConds-UNION (uni n) w A B A1 B1 A2 B2 x x₁ eqtA eqtB extA extB inda indb
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqtA w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqtA w1 e1)

    indb : ∀𝕎 w (λ w1 e1 → TSP (eqtB w1 e1))
    indb w1 e1 = typeSysConds-aux n ind w1 B1 B2 (eqtB w1 e1)

typeSysConds-aux n ind w A B (EQTSQUASH A1 A2 x x₁ eqtA exta) =
  typeSysConds-TSQUASH (uni n) w A B A1 A2 x x₁ eqtA exta inda
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqtA w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqtA w1 e1)

--typeSysConds-aux n ind w A B (EQTDUM A1 A2 x x₁ eqta) = {!!}

typeSysConds-aux n ind w A B (EQFFDEFS A1 A2 x1 x2 x x₁ eqta exta eqx) =
  typeSysConds-FFDEFS (uni n) w A B A1 A2 x1 x2 x x₁ eqta exta inda eqx
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqta w1 e1)

typeSysConds-aux n ind w A B (EQTUNIV m p c₁ c₂) =
  is-TSP-univs-eqUnivi n ind w A B m p c₁ c₂

typeSysConds-aux n ind w A B (EQTLIFT A1 A2 x x₁ eqtA) = ?
{--  typeSysConds-TSQUASH (uni n) w A B A1 A2 x x₁ eqtA exta inda
  where
    inda : ∀𝕎 w (λ w1 e1 → TSP (eqtA w1 e1))
    inda w1 e1 = typeSysConds-aux n ind w1 A1 A2 (eqtA w1 e1)--}

typeSysConds-aux n ind w A B (EQTBAR x) =
  typeSysConds-BAR (uni n) (is-uni-uni n) w A B x ind'
  where
    ind' : inbar' w x (λ w1 e1 z → TSP z)
    ind' = Bar.∀𝕎-inBar-inBar' inOpenBar-Bar x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' A B) (at : atbar x w' e' z) → TSP z)
        aw w1 e1 z at = typeSysConds-aux n ind w1 A B z




eqTypes-inbar : {u : univs} {w : 𝕎·} {a b c d : CTerm} {F : wPred w}
                → ∀𝕎 w (λ w1 e1 → F w1 e1 → eqTypes u w1 a b → eqTypes u w1 c d)
                → inbar w F
                → eqTypes u w a b
                → eqTypes u w c d
eqTypes-inbar {u} {w} {a} {b} {c} {d} {F} aw i e =
  EQTBAR (Bar.∀𝕎-inBarFunc inOpenBar-Bar q i)
  where
    q : ∀𝕎 w (λ w' e' → F w' e' → eqTypes u w' c d)
    q w1 e1 f = aw w1 e1 f (eqTypes-mon u e w1 e1)


eqUnivi-mon : (n : ℕ) → mon (eqUnivi n)
eqUnivi-mon n e w1 e1 = Bar.↑inBar inOpenBar-Bar e e1




{--
eqInUnivi→ : {n : ℕ} {w : 𝕎·} {A B : CTerm} → eqInUnivi n w A B → Σ ℕ (λ m → m < n × inbar w (λ w' _ → eqTypes (uni m) w' A B))
eqInUnivi→ {suc n} {w} {A} {B} ({--inj₁--} x) = n , n<1+n n , x
{--eqInUnivi→ {suc n} {w} {A} {B} (inj₂ y) = fst ind , <-trans (fst (snd ind)) (n<1+n n) , snd (snd ind)
  where
    ind : Σ ℕ (λ m → m < n × eqTypes (uni m) w A B)
    ind = eqInUnivi→ y--}
--}



{--mon-univs-uni : (n : ℕ) → mon-univs (uni n)
mon-univs-uni n {a} {b} {w} h w1 e1 =
  Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (Bar.↑inBar inOpenBar-Bar h e1)
  where
    aw : ∀𝕎 w1 (λ w' e' → ↑wPred (λ w'' e → a #⇛ #UNIV n at w'' × b #⇛ #UNIV n at w'') e1 w' e'
                          → a #⇛ #UNIV n at w' × b #⇛ #UNIV n at w')
    aw w' e' x = x--}



→inbar× : {w : 𝕎·} {f g : wPred w}
           → inbar w f
           → inbar w g
           → inbar w (λ w' e' → f w' e' × g w' e')
→inbar× {w} {f} {g} i j = Bar.inBarFunc inOpenBar-Bar (Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' a b → (a , b)) i) j



inbar×→₁ : {w : 𝕎·} {f g : wPred w}
           → inbar w (λ w' e' → f w' e' × g w' e')
           → inbar w f
inbar×→₁ {w} {f} {g} i = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' → fst) i



inbar×→₂ : {w : 𝕎·} {f g : wPred w}
           → inbar w (λ w' e' → f w' e' × g w' e')
           → inbar w g
inbar×→₂ {w} {f} {g} i = Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w' e' → snd) i



comp-ind-ℕ-aux : (P : ℕ → Set₁)
                 → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                 → (n m : ℕ) → m < n → P m
comp-ind-ℕ-aux P ind (suc n) m (_≤_.s≤s z) with m≤n⇒m<n∨m≡n z
... | inj₁ q = comp-ind-ℕ-aux P ind n m q
... | inj₂ q rewrite q = ind n (comp-ind-ℕ-aux P ind n)


comp-ind-ℕ : (P : ℕ → Set₁)
              → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
              → (n : ℕ) → P n
comp-ind-ℕ P ind n = comp-ind-ℕ-aux P ind (suc n) n (_≤_.s≤s ≤-refl)


{--
is-TSP-univs-uni : (n : ℕ) → is-TSP-univs (uni n)
is-TSP-univs-uni n = comp-ind-ℕ (λ n → is-TSP-univs (uni n)) h n
  where
    h : (i : ℕ) → ((m : ℕ) → m < i → is-TSP-univs (uni m)) → is-TSP-univs (uni i)
    h i ind w A B x = {!!} --is-TSP-univs-eqUnivi i ind w A B x
--}



typeSysConds : (n : ℕ) → is-TSP-univs (uni n)
typeSysConds n = comp-ind-ℕ (λ n → is-TSP-univs (uni n)) typeSysConds-aux n



TEQsym-eqtypes : TEQsym eqtypes
TEQsym-eqtypes w A B (n , h) = n , TSP.tsym (typeSysConds n w A B h)


{--
eqTypes-uni-mon-suc : {n : ℕ} {w : 𝕎·} {A B : CTerm}
                      → eqTypes (uni n) w A B
                      → eqTypes (uni (suc n)) w A B
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTNAT x x₁) = EQTNAT x x₁
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTQNAT x x₁) = EQTQNAT x x₁
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = EQTLT a1 a2 b1 b2 x x₁ x₂ x₃
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTFREE x x₁) = EQTFREE x x₁
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI
    A1 B1 A2 B2 x x₁
    {!!}
    {!!}
    ? ?
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTUNIV x) = {!!}
eqTypes-uni-mon-suc {n} {w} {A} {B} (EQTBAR x) = {!!}
--}


TEQsym-equalTypes : (n : ℕ) → TEQsym (equalTypes n)
TEQsym-equalTypes n w A B h = TSP.tsym (typeSysConds n w A B h)


TEQtrans-equalTypes : (n : ℕ) → TEQtrans (equalTypes n)
TEQtrans-equalTypes n w A B C h q =
  TSP.ttrans (typeSysConds n w A B h) C q


EQTsym-equalInType : (n : ℕ) → EQTsym (equalInType n)
EQTsym-equalInType n w A a b (teq , eqi) =
  teq , TSP.isym (typeSysConds n w A A teq) a b eqi


EQTtrans-equalInType : (n : ℕ) → EQTtrans (equalInType n)
EQTtrans-equalInType n w A a b c (teq₁ , eqi₁) (teq₂ , eqi₂) =
  teq₁ , TSP.itrans
           (typeSysConds n w A A teq₁)
           a b c
           eqi₁
           (TSP.extl1 (typeSysConds n w A A teq₂) A teq₁ b c eqi₂)


TEQrefl : TEQ → Set₁
TEQrefl τ = (w : 𝕎·) (A B : CTerm) → τ w A B → τ w A A


TEQrefl-rev : TEQ → Set₁
TEQrefl-rev τ = (w : 𝕎·) (A B : CTerm) → τ w A B → τ w B B



TEQrefl-equalTypes : (n : ℕ) → TEQrefl (equalTypes n)
TEQrefl-equalTypes n w A B h =
  TEQtrans-equalTypes n w A B A h (TEQsym-equalTypes n w A B h)


TEQrefl-rev-equalTypes : (n : ℕ) → TEQrefl-rev (equalTypes n)
TEQrefl-rev-equalTypes n w A B h =
  TEQtrans-equalTypes n w B A B (TEQsym-equalTypes n w A B h) h


TSext-equalTypes-equalInType : (n : ℕ) → TSext (equalTypes n) (equalInType n)
TSext-equalTypes-equalInType n w A B a b h (teq , eqi) =
  TEQrefl-rev-equalTypes n w A B h ,
  TSP.extr1
    (typeSysConds n w A B h)
    B (TEQrefl-rev-equalTypes n w A B h) a b
    (TSP.extl1 (typeSysConds n w A A teq) B h a b eqi)


typeSys : (n : ℕ) → TS (equalTypes n) (equalInType n)
typeSys n =
  mkts
    (TEQsym-equalTypes n)
    (TEQtrans-equalTypes n)
    (EQTsym-equalInType n)
    (EQTtrans-equalInType n)
    (TSext-equalTypes-equalInType n)



{--
-- Those need to be packaged as we did in Coq
eqTypes-sym : (u : univs) → TEQsym (eqTypes u)
eqInType-sym : (u : univs) (w : 𝕎·) (A B a b : CTerm) (eqt : eqTypes u w A B)
               → eqInType u w eqt a b
               → eqInType u w eqt b a
eqType-refl : (u : univs) (w : 𝕎·) (A B : CTerm)
              → eqTypes u w A B
              → eqTypes u w A A
eqInType-refl : (u : univs) (w : 𝕎·) (A B a b : CTerm) (eqt : eqTypes u w A B)
                → eqInType u w eqt a b
                → eqInType u w eqt a a
eqType-pres-eqInType : (u : univs) (w : 𝕎·) (A B C D a b : CTerm)
                       (eqt1 : eqTypes u w A B) (eqt2 : eqTypes u w C D)
                       → eqTypes u w B C
                       → eqInType u w eqt1 a b
                       → eqInType u w eqt2 a b
eqTypes-trans : (u : univs) (w : 𝕎·) (A B C : CTerm) → eqTypes u w A B → eqTypes u w B C → eqTypes u w A C


eqTypes-sym u w A B (EQTNAT x x₁) = EQTNAT x₁ x
eqTypes-sym u w A B (EQTQNAT x x₁) = EQTQNAT x₁ x
eqTypes-sym u w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a2 a1 b2 b1 x₁ x (strongMonEq-sym x₂) (strongMonEq-sym x₃)
eqTypes-sym u w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a2 a1 b2 b1 x₁ x (weakMonEq-sym x₂) (weakMonEq-sym x₃)
eqTypes-sym u w A B (EQTFREE x x₁) = EQTFREE x₁ x
eqTypes-sym u w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI
    A2 B2 A1 B1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqta w1 e1))
    (λ w1 e1 a b eqi →
      eqTypes-sym
        u w1 (sub0 b B1) (sub0 a B2)
        (eqtb w1 e1 b a
              (eqInType-sym u w1 A1 A2 a b (eqta w1 e1)
                (eqType-pres-eqInType u w1 A2 A1 A1 A2 a b
                  (eqTypes-sym u w1 A1 A2 (eqta w1 e1))
                  (eqta w1 e1)
                  (eqType-refl u w1 A1 A2 (eqta w1 e1))
                  eqi))))
    ? ?
eqTypes-sym u w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTSUM
    A2 B2 A1 B1 x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A1 A2 (eqta w1 e1))
    (λ w1 e1 a b eqi →
      eqTypes-sym
        u w1 (sub0 b B1) (sub0 a B2)
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
        u w1 (sub0 b B1) (sub0 a B2)
        (eqtb w1 e1 b a
              (eqInType-sym u w1 A1 A2 a b (eqta w1 e1)
                (eqType-pres-eqInType u w1 A2 A1 A1 A2 a b
                  (eqTypes-sym u w1 A1 A2 (eqta w1 e1))
                  (eqta w1 e1)
                  (eqType-refl u w1 A1 A2 (eqta w1 e1))
                  eqi))))
eqTypes-sym u w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) =
  EQTEQ
    b1 a1 b2 a2 B₁ A₁ x₁ x
    (λ w1 e1 → eqTypes-sym u w1 A₁ B₁ (eqtA w1 e1))
    (λ w1 e1 → {!!}) --eqType-sym-pres-rev u w1 A₁ B₁ b1 a1 (eqtA w1 e1) (eqInType-sym u w1 A₁ B₁ a1 b1 (eqtA w1 e1) (eqt1 w1 e1)))
    (λ w1 e1 → {!!}) --eqType-sym-pres-rev u w1 A₁ B₁ b2 a2 (eqtA w1 e1) (eqInType-sym u w1 A₁ B₁ a2 b2 (eqtA w1 e1) (eqt2 w1 e1)))
eqTypes-sym u w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) =
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
  Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 → strongMonEq-sym) h
eqInType-sym u w A B a b (EQTQNAT x x₁) h =
  Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 → weakMonEq-sym) h
eqInType-sym u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) h =
  Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 z → z) h
eqInType-sym u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) h = {!!}
eqInType-sym u w A B a b (EQTFREE x x₁) h = {!!}
eqInType-sym u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) h =
  Bar.∀𝕎-inBarFunc
    inOpenBar-Bar
    h₁
    h
  where
    h₁ : ∀𝕎 w
           (λ w' e'
             → ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) → eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY a a1) (APPLY b a2))
             → (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) → eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY b a1) (APPLY a a2))
    h₁ w1 e1 z a₁ b₁ eqa =
      eqInType-sym
        u w1 (sub0 a₁ B1) (sub0 b₁ B2) (APPLY a b₁) (APPLY b a₁)
        (eqtb w1 e1 a₁ b₁ eqa)
        (eqType-pres-eqInType u w1 (sub0 b₁ B1) (sub0 a₁ B2) (sub0 a₁ B1) (sub0 b₁ B2) (APPLY a b₁) (APPLY b a₁)
          (eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa))
          (eqtb w1 e1 a₁ b₁ eqa)
          (eqTypes-sym u w1 (sub0 a₁ B1) (sub0 a₁ B2) (eqtb w1 e1 a₁ a₁ (eqInType-refl u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa)))
          h₂)
        where
          h₂ : eqInType u w1 (eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa)) (APPLY a b₁) (APPLY b a₁)
          h₂ = z b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa)
{--      eqInType-sym
        u w1 (sub0 b₁ B1) (sub0 a₁ B2) (APPLY a b₁) (APPLY b a₁)
        {!!} --(eqtb w1 e1 b₁ a₁ (eqInType-sym-rev u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa))
        {!!}) --(z b₁ a₁ (eqInType-sym-rev u w1 A1 A2 a₁ b₁ (eqta w1 e1) eqa))) --}
eqInType-sym u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) h = {!!}
eqInType-sym u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) h = {!!}
eqInType-sym u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) h = {!!}
eqInType-sym u w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) h = {!!}
eqInType-sym u w A B a b (EQTUNIV x) h = {!!}
eqInType-sym u w A B a b (EQTBAR x) h = {!!}

eqType-refl u w A B (EQTNAT x x₁) = EQTNAT x x
eqType-refl u w A B (EQTQNAT x x₁) = {!!}
eqType-refl u w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
eqType-refl u w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
eqType-refl u w A B (EQTFREE x x₁) = {!!}
eqType-refl u w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI
    A1 B1 A1 B1 x x
    (λ w1 e1 → eqType-refl u w1 A1 A2 (eqta w1 e1))
    h
    ? ?
  where
    h : ∀𝕎 w (λ w' e →
         (a1 a2 : CTerm) → eqInType u w' (eqType-refl u w' A1 A2 (eqta w' e)) a1 a2
         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B1))
    h w1 e1 a1 a2 eqa = h₀
      where
        h₃ : eqTypes u w1 A1 A1
        h₃ = eqType-refl u w1 A1 A2 (eqta w1 e1)

        h₂ : eqInType u w1 (eqta w1 e1) a1 a2
        h₂ = eqType-pres-eqInType u w1 A1 A1 A1 A2 a1 a2 (eqType-refl u w1 A1 A2 (eqta w1 e1)) (eqta w1 e1) h₃ eqa

        h₁ : eqTypes u w1 (sub0 a1 B1) (sub0 a2 B2)
        h₁ = eqtb w1 e1 a1 a2 h₂

        h₆ : eqInType u w1 (eqta w1 e1) a2 a1
        h₆ = eqInType-sym u w1 A1 A2 a1 a2 (eqta w1 e1) h₂

        h₅ : eqInType u w1 (eqta w1 e1) a2 a2
        h₅ = eqInType-refl u w1 A1 A2 a2 a1 (eqta w1 e1) h₆

        h₄ : eqTypes u w1 (sub0 a2 B1) (sub0 a2 B2)
        h₄ = eqtb w1 e1 a2 a2 h₅

        h₇ : eqTypes u w1 (sub0 a2 B2) (sub0 a2 B1)
        h₇ = eqTypes-sym u w1 (sub0 a2 B1) (sub0 a2 B2) h₄

        h₀ : eqTypes u w1 (sub0 a1 B1) (sub0 a2 B1)
        h₀ = eqTypes-trans u w1 (sub0 a1 B1) (sub0 a2 B2) (sub0 a2 B1) h₁ h₇


eqType-refl u w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqType-refl u w A B (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqType-refl u w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) = {!!}
eqType-refl u w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) = {!!}
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
  Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 → strongMonEq-sym) h
eqInType-sym-rev u w A B a b (EQTQNAT x x₁) h =
  Bar.∀𝕎-inBarFunc inOpenBar-Bar (λ w1 e1 → weakMonEq-sym) h
eqInType-sym-rev u w A B a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) h =
  Bar.∀𝕎-inBarFunc
    inOpenBar-Bar
    (λ w1 e1 (lift (n , m , c₁ , c₂ , d)) →
      lift (n , m ,
              strongMonEq-pres-⇓ (strongMonEq-sym (strongMonEq-mon x₂ w1 e1)) c₁ ,
              strongMonEq-pres-⇓ (strongMonEq-sym (strongMonEq-mon x₃ w1 e1)) c₂ ,
              d))
    h
eqInType-sym-rev u w A B a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) h = {!!}
eqInType-sym-rev u w A B a b (EQTFREE x x₁) h = {!!}
eqInType-sym-rev u w A B a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) h =
  Bar.∀𝕎-inBarFunc
    inOpenBar-Bar
    (λ w1 e1 z a₁ b₁ eqa →
      eqInType-sym-rev
        u w1 (sub0 b₁ B1) (sub0 a₁ B2) (APPLY a b₁) (APPLY b a₁)
        {!eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqa w1 e1))!} --(eqtb w1 e1 b₁ a₁ (eqInType-sym u w1 A1 A2 a₁ b₁ (eqa w1 e1)))  -- eqTypes u w1 (sub0 b₁ B1) (sub0 a₁ B2)
        {!!})
    h
eqInType-sym-rev u w A B a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym-rev u w A B a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) h = {!!}
eqInType-sym-rev u w A B a b (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) h = {!!}
eqInType-sym-rev u w A B a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) h = {!!}
eqInType-sym-rev u w A B a b (EQTSQUASH A1 A2 x x₁ eqtA) h = {!!}
eqInType-sym-rev u w A B a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) h = {!!}
eqInType-sym-rev u w A B a b (EQTUNIV x) h = {!!}
eqInType-sym-rev u w A B a b (EQTBAR x) h = {!!}
--}


{--if-equalInType-NAT : (u : ℕ) (I : Inh) (w : 𝕎·) (t₁ t₂ : CTerm)
                     → equalInType u I w NAT t₁ t₂
                     → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
if-equalInType-NAT u I w t₁ t₂ (EQTNAT x x₁ , eqi) = eqi
if-equalInType-NAT u I w t₁ t₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (NATneqQNAT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (NATneqLT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (NATneqQLT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTFREE x x₁ , eqi) = ⊥-elim (NATneqFREE (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (NATneqPI (compAllVal I x₁ tt))
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


¬strongMonEq01 : (I : Inh) (w : 𝕎·) → ¬ strongMonEq I w (NUM 0) (NUM 1)
¬strongMonEq01 I w (n , c₁ , c₂) = eb
  where
    ea : NUM 0 ≡ NUM 1
    ea rewrite compAllVal I c₁ tt | compAllVal I c₂ tt = refl

    eb : ⊥
    eb with ea
    ... | ()


VOID : CTerm
VOID = EQ (NUM 0) (NUM 1) NAT


weak-consistency : (w : 𝕎·) → ¬ Σ Term (λ t → eqintype w VOID t t)
weak-consistency w (t , u , n , k , c) = ¬strongMonEq01 I w2 ea5
  where
    ea1 : eqintypeN u n (k + n) w VOID t t
    ea1 = c n ≤-refl

    I : Inh
    I = inhN u n (k + n)

    ea2 : inOpenBar I w (λ w' e' → [ I ] t ⇛ AX at w' × [ I ] t ⇛ AX at w' × equalInType u I w' NAT (NUM 0) (NUM 1))
    ea2 = if-equalInType-EQ u I w NAT (NUM 0) (NUM 1) t t ea1

    w1 : 𝕎·
    w1 = proj₁ (ea2 w ([]≽-refl I w))

    e1 : [ I ] w1 ⪰ w
    e1 = proj₁ (proj₂ (ea2 w ([]≽-refl I w)))

    ea3 : equalInType u I w1 NAT (NUM 0) (NUM 1)
    ea3 = proj₂ (proj₂ (proj₂ (proj₂ (ea2 w ([]≽-refl I w))) w1 ([]≽-refl I w1)))

    ea4 : inOpenBar I w1 (λ w1 e1 → strongMonEq I w1 (NUM 0) (NUM 1))
    ea4 = if-equalInType-NAT u I w1 (NUM 0) (NUM 1) ea3

    w2 : 𝕎·
    w2 = proj₁ (ea4 w1 ([]≽-refl I w1))

    e2 : [ I ] w2 ⪰ w1
    e2 = proj₁ (proj₂ (ea4 w1 ([]≽-refl I w1)))

    ea5 : strongMonEq I w2 (NUM 0) (NUM 1)
    ea5 = proj₂ (proj₂ (ea4 w1 ([]≽-refl I w1))) w2 ([]≽-refl I w2)
--}
\end{code}


%Let us now prove further results about this semantics


\begin{code}[hide]
{--
-- ---------------------------------
-- Some simple lemmas
∀𝕎impliesinOpenBar : {I : Inh} {w : 𝕎·} {f : wPred I w} → ∀𝕎 I w f → inOpenBar I w f
∀𝕎impliesinOpenBar {I} {w} {f} h w1 e1 = (w1 , ([]≽-refl I _ , λ w2 e2 → h w2 ([]≽-trans {I} e2 _)))

eqTypesNAT : (w : 𝕎·) (I : Inh) (u : univs) → eqTypes u I w NAT NAT
eqTypesNAT w I u =
  EQTNAT (compAllRefl I NAT w) (compAllRefl I NAT w)

strongMonEqN0 : (I : Inh) (w : 𝕎·) → strongMonEq I w N0 N0
strongMonEqN0 I w =  (0 , (compAllRefl I N0 w , compAllRefl I N0 w))

allInOpenBarStrongMonEqN0 : (I : Inh) (w : 𝕎·) → ∀𝕎 I w (λ w' e → inOpenBar I w' (λ w'' _ → strongMonEq I w'' N0 N0))
allInOpenBarStrongMonEqN0 I w w1 e1 w2 e2 = (w2 , ([]≽-refl I _ , λ w3 e3 → strongMonEqN0 I w3))

eqTypesTRUE : (w : 𝕎·) (I : Inh) (u : univs) → eqTypes u I w TRUE TRUE
eqTypesTRUE w I u =
  EQTEQ N0 N0 N0 N0 NAT NAT
        (compAllRefl I (EQ N0 N0 NAT) w)
        (compAllRefl I (EQ N0 N0 NAT) w)
        (λ w1 e1 → eqTypesNAT _ _ _)
        (allInOpenBarStrongMonEqN0 I w)
        (allInOpenBarStrongMonEqN0 I w)



-- wPredExtIrr
wPredExtIrr-equalInType : (u : ℕ) (I1 I2 : Inh) (w : 𝕎·) (T a b : CTerm)
                          → wPredExtIrr {I1} {w} (λ w1 e1 → equalInType u I2 w1 T a b)
wPredExtIrr-equalInType u I1 I2 w T a b w' e1 e2 h = h


wPredExtIrr-eqTypes : (u : univs) (I1 I2 : Inh) (w : 𝕎·) (A B : CTerm)
                      → wPredExtIrr {I1} {w} (λ w1 e1 → eqTypes u I2 w1 A B)
wPredExtIrr-eqTypes u I1 I2 w A B w' e1 e2 h = h




eqUnivi-mon : (i : ℕ) → mon (eqUnivi i)
eqUnivi-mon i {a} {b} I {w} h w1 e1 =
  inOpenBar-mon I {w1} {w} {λ w' _ → [ I ] a #⇛ (#UNIV i) at w' × [ I ] b #⇛ (#UNIV i) at w'} (λ w' e2 e3 h → h) e1 h


eqInUnivi-mon : (i : ℕ) → mon (eqInUnivi i)
eqInUnivi-mon (suc i) {a} {b} I {w} (inj₁ x) w1 e1 =
  inj₁ (eqTypes-mon (i , eqUnivi i , eqInUnivi i) (eqUnivi-mon i) I x w1 e1)
eqInUnivi-mon (suc i) {a} {b} I {w} (inj₂ y) w1 e1 =
  inj₂ (eqInUnivi-mon i I y w1 e1)



-- SET
SETinj1 : {a b : CTerm} {c d : CTerm} → SET a c ≡ SET b d → a ≡ b
SETinj1 refl =  refl

SETinj2 : {a b : CTerm} {c d : CTerm} → SET a c ≡ SET b d → c ≡ d
SETinj2 refl =  refl


-- SET
SETneqNAT : {a : CTerm} {b : CTerm} → ¬ (SET a b) ≡ NAT
SETneqNAT {a} {b} ()

SETneqQNAT : {a : CTerm} {b : CTerm} → ¬ (SET a b) ≡ QNAT
SETneqQNAT {a} {b} ()

SETneqLT : {a : CTerm} {b : CTerm} {c d : CTerm} → ¬ (SET a b) ≡ LT c d
SETneqLT {a} {b} {c} {d} ()

SETneqQLT : {a : CTerm} {b : CTerm} {c d : CTerm} → ¬ (SET a b) ≡ QLT c d
SETneqQLT {a} {b} {c} {d} ()

SETneqFREE : {a : CTerm} {b : CTerm} → ¬ (SET a b) ≡ FREE
SETneqFREE {a} {b} ()

SETneqPI : {a : CTerm} {b : CTerm} {c : CTerm} {d : CTerm} → ¬ (SET a b) ≡ PI c d
SETneqPI {a} {b} {c} {d} ()

SETneqSUM : {a : CTerm} {b : CTerm} {c : CTerm} {d : CTerm} → ¬ (SET a b) ≡ SUM c d
SETneqSUM {a} {b} {c} {d} ()

SETneqUNION : {a : CTerm} {b : CTerm} {c : CTerm} {d : CTerm} → ¬ (SET a b) ≡ UNION c d
SETneqUNION {a} {b} {c} {d} ()

SETneqTSQUASH : {a : CTerm} {b : CTerm} {c : CTerm} → ¬ (SET a b) ≡ TSQUASH c
SETneqTSQUASH {a} {b} {c} ()

SETneqEQ : {a : CTerm} {b : CTerm} {c d e : CTerm} → ¬ (SET a b) ≡ EQ c d e
SETneqEQ {a} {b} {c} {d} {e} ()

SETneqFFDEFS : {a : CTerm} {b : CTerm} {c d : CTerm} → ¬ (SET a b) ≡ FFDEFS c d
SETneqFFDEFS {a} {b} {c} {d} ()

SETneqLOWER : {a : CTerm} {b : CTerm} {c : CTerm} → ¬ (SET a b) ≡ LOWER c
SETneqLOWER {a} {b} {c} ()

SETneqSHRINK : {a : CTerm} {b : CTerm} {c : CTerm} → ¬ (SET a b) ≡ SHRINK c
SETneqSHRINK {a} {b} {c} ()

SETneqUNIV : {a : CTerm} {b : CTerm} {n : ℕ} → ¬ (SET a b) ≡ UNIV n
SETneqUNIV {a} {b} {n} ()


-- LOWER
LOWERneqNAT : {a : CTerm} → ¬ (LOWER a) ≡ NAT
LOWERneqNAT {a} ()

LOWERneqQNAT : {a : CTerm} → ¬ (LOWER a) ≡ QNAT
LOWERneqQNAT {a} ()

LOWERneqLT : {a : CTerm} {c d : CTerm} → ¬ (LOWER a) ≡ LT c d
LOWERneqLT {a} {c} {d} ()

LOWERneqQLT : {a : CTerm} {c d : CTerm} → ¬ (LOWER a) ≡ QLT c d
LOWERneqQLT {a} {c} {d} ()

LOWERneqFREE : {a : CTerm} → ¬ (LOWER a) ≡ FREE
LOWERneqFREE {a} ()

LOWERneqPI : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (LOWER a) ≡ PI c d
LOWERneqPI {a} {c} {d} ()

LOWERneqSUM : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (LOWER a) ≡ SUM c d
LOWERneqSUM {a} {c} {d} ()

LOWERneqSET : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (LOWER a) ≡ SET c d
LOWERneqSET {a} {c} {d} ()

LOWERneqUNION : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (LOWER a) ≡ UNION c d
LOWERneqUNION {a} {c} {d} ()

LOWERneqTSQUASH : {a : CTerm} {c : CTerm} → ¬ (LOWER a) ≡ TSQUASH c
LOWERneqTSQUASH {a} {c} ()

LOWERneqEQ : {a : CTerm} {c d e : CTerm} → ¬ (LOWER a) ≡ EQ c d e
LOWERneqEQ {a} {c} {d} {e} ()

LOWERneqFFDEFS : {a : CTerm} {c d : CTerm} → ¬ (LOWER a) ≡ FFDEFS c d
LOWERneqFFDEFS {a} {c} {d} ()

LOWERneqUNIV : {a : CTerm} {n : ℕ} → ¬ (LOWER a) ≡ UNIV n
LOWERneqUNIV {a} {n} ()

LOWERneqSHRINK : {a b : CTerm} → ¬ LOWER a ≡ SHRINK b
LOWERneqSHRINK {a} {b} ()

LOWERinj : {a b : CTerm} → LOWER a ≡ LOWER b → a ≡ b
LOWERinj refl =  refl

compAllLOWER : {I : Inh} {w : 𝕎·} {a b : CTerm} → [ I ] LOWER a ⇛ LOWER b at w → a ≡ b
compAllLOWER {I} {w} {a} {b} e = LOWERinj (compAllVal I e tt)


-- SHRINK
SHRINKneqNAT : {a : CTerm} → ¬ (SHRINK a) ≡ NAT
SHRINKneqNAT {a} ()

SHRINKneqQNAT : {a : CTerm} → ¬ (SHRINK a) ≡ QNAT
SHRINKneqQNAT {a} ()

SHRINKneqLT : {a : CTerm} {c d : CTerm} → ¬ (SHRINK a) ≡ LT c d
SHRINKneqLT {a} {c} {d} ()

SHRINKneqQLT : {a : CTerm} {c d : CTerm} → ¬ (SHRINK a) ≡ QLT c d
SHRINKneqQLT {a} {c} {d} ()

SHRINKneqFREE : {a : CTerm} → ¬ (SHRINK a) ≡ FREE
SHRINKneqFREE {a} ()

SHRINKneqPI : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (SHRINK a) ≡ PI c d
SHRINKneqPI {a} {c} {d} ()

SHRINKneqSUM : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (SHRINK a) ≡ SUM c d
SHRINKneqSUM {a} {c} {d} ()

SHRINKneqSET : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (SHRINK a) ≡ SET c d
SHRINKneqSET {a} {c} {d} ()

SHRINKneqUNION : {a : CTerm} {c : CTerm} {d : CTerm} → ¬ (SHRINK a) ≡ UNION c d
SHRINKneqUNION {a} {c} {d} ()

SHRINKneqTSQUASH : {a : CTerm} {c : CTerm} → ¬ (SHRINK a) ≡ TSQUASH c
SHRINKneqTSQUASH {a} {c} ()

SHRINKneqEQ : {a : CTerm} {c d e : CTerm} → ¬ (SHRINK a) ≡ EQ c d e
SHRINKneqEQ {a} {c} {d} {e} ()

SHRINKneqFFDEFS : {a : CTerm} {c d : CTerm} → ¬ (SHRINK a) ≡ FFDEFS c d
SHRINKneqFFDEFS {a} {c} {d} ()

SHRINKneqUNIV : {a : CTerm} {n : ℕ} → ¬ (SHRINK a) ≡ UNIV n
SHRINKneqUNIV {a} {n} ()

SHRINKneqLOWER : {a b : CTerm} → ¬ SHRINK a ≡ LOWER b
SHRINKneqLOWER {a} {b} ()

SHRINKinj : {a b : CTerm} → SHRINK a ≡ SHRINK b → a ≡ b
SHRINKinj refl =  refl

compAllSHRINK : {I : Inh} {w : 𝕎·} {a b : CTerm} → [ I ] SHRINK a ⇛ SHRINK b at w → a ≡ b
compAllSHRINK {I} {w} {a} {b} e = SHRINKinj (compAllVal I e tt)



closedlamAX : # lamAX
closedlamAX v ()

closedAX : # AX
closedAX v ()

sublamAX : (t : CTerm) → sub t lamAX ≡ lamAX
sublamAX t = subNotIn t lamAX closedAX

subAX : (t : CTerm) → sub t AX ≡ AX
subAX t = subNotIn t AX closedAX

closedNAT : # NAT
closedNAT v ()

closedLNAT : # LNAT
closedLNAT v ()

subNAT : (t : CTerm) → sub t NAT ≡ NAT
subNAT t = subNotIn t NAT closedNAT

subLNAT : (t : CTerm) → sub t LNAT ≡ LNAT
subLNAT t = subNotIn t LNAT closedLNAT

eqFun : {a b c d : CTerm} → a ≡ b → c ≡ d → FUN a c ≡ FUN b d
eqFun {a} {b} {c} {d} e f rewrite e rewrite f = refl

closedLe : {u : CTerm} → # u → (v : Var) → ((w : Var) → v ≤ w → w # u)
closedLe {u} c v w j = c w

subacFun : (t : CTerm) → # t → sub t acFun ≡ FUN (acHypPi t) (acConclP t)
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

closedfvarsnil : (t : CTerm) → # t → fvars t ≡ []
closedfvarsnil t c = notinnil (fvars t) c

innilfalse : {A : Set} (v : A) → v ∈ [] → ⊥
innilfalse {A} v ()

closedacConclP : (P : CTerm) → # P → # (acConclP P)
closedacConclP P c v i
  rewrite lowerVarsApp (fvars P ++ 0 ∷ []) (1 ∷ 0 ∷ [])
  rewrite lowerVarsApp (fvars P) (0 ∷ [])
  rewrite lowerVarsApp (lowerVars (fvars P) ++ []) (0 ∷ [])
  rewrite lowerVarsApp (lowerVars (lowerVars (fvars P) ++ [])) (0 ∷ [])
  rewrite closedfvarsnil P c = innilfalse v i

equalInType-eqTypes : (u : ℕ) (I : Inh) (w : 𝕎·) (A a b : CTerm)
                      → equalInType u I w A a b
                      → equalTypes u I w A A
equalInType-eqTypes u I w A a b (eqt , eqi) = eqt

inOpenBarEqualInType-inOpenBarEqTypes : (u : ℕ) (I : Inh) (w : 𝕎·) (A a b : CTerm)
                                        → inOpenBar I w (λ w' _ → equalInType u I w' A a b)
                                        → inOpenBar I w (λ w' _ → equalTypes u I w' A A)
inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h w1 e1 =
  let (w2 , (e2 , eqt2)) = h w1 e1 in
  (w2 , (e2 , λ w3 e3 → fst (eqt2 w3 e3)))

inOpenBarStrongMonEqNUM : (I : Inh) (w : 𝕎·) (n : ℕ)
                          → inOpenBar I w (λ w1 e1 → strongMonEq I w1 (NUM n) (NUM n))
inOpenBarStrongMonEqNUM I w n w1 e1 =
  (w1 , ([]≽-refl I w1 , λ w2 e2 → (n , (compAllRefl I (NUM n) w2 , compAllRefl I (NUM n) w2))))

equalInTypeNAT : (u : ℕ) (I : Inh) (w : 𝕎·) (t₁ t₂ : CTerm)
                → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT u I w t₁ t₂ e = (eqTypesNAT w I (uni u) , e)

equalInTypeNAT2 : (u : ℕ) (I : Inh) (w : 𝕎·) (t₁ t₂ : CTerm)
                → strongMonEq I w t₁ t₂
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT2 u I w t₁ t₂ e =
  equalInTypeNAT u I w t₁ t₂
    λ w1 e1 → (w1 , []≽-refl I w1 , λ w2 e2 → strongMonEq-mon I e w2 ([]≽-trans {I} e2 e1))

numInNAT : (u : ℕ) (I : Inh) (w : 𝕎·) (n : ℕ)
           → equalInType u I w NAT (NUM n) (NUM n)
numInNAT u I w n = equalInTypeNAT u I w (NUM n) (NUM n) (inOpenBarStrongMonEqNUM I w n)


inOpenBarMP : (I : Inh) (w : 𝕎·) (f g : wPred I w)
              → ∀𝕎 I w (λ w1 e1 → f w1 e1 → g w1 e1)
              → inOpenBar I w f → inOpenBar I w g
inOpenBarMP I w f g i j w1 e1 =
  let (w2 , (e2 , h)) = j w1 e1 in
  (w2 , (e2 , λ w3 e3 → let z = h w3 e3 in i w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2 e1)) z))

inOpenBarIdem : (I : Inh) (w : 𝕎·) (f : wPred I w) (c : wPredExtIrr {I} {w} f)
                → inOpenBar I w (λ w1 e1 → inOpenBar I w1 (↑wPred I f e1))
                → inOpenBar I w f
inOpenBarIdem I w f c i w1 e1 =
  let (w2 , (e2 , i1)) = i w1 e1 in
  let (w3 , (e3 , i2)) = i1 _ ([]≽-refl I _) _ ([]≽-refl I _) in
  (w3 , ([]≽-trans {I} e3 e2 , λ w4 e4 → let i3 = i2 w4 e4 in c w4 _ _ i3))


substEqTeq : (u : univs) (I1 I2 : Inh) (w : 𝕎·) (A1 A2 B1 B2 a₁ a₂ : CTerm)
             (eqt : eqTypes u I1 w A1 B1) (eqi : eqInType u I1 w eqt a₁ a₂)
             → I1 ≡ I2
             → A1 ≡ A2
             → B1 ≡ B2
             → Σ (eqTypes u I2 w A2 B2) (λ eqt → eqInType u I2 w eqt a₁ a₂)
substEqTeq u I1 I2 w A1 A2 B1 B2 a₁ a₂ eqt eqi e1 e2 e3 rewrite e1 | e2 | e3 = (eqt , eqi)

strongMonEqsym : (I : Inh) {w : 𝕎·} {a b : CTerm} → strongMonEq I w a b → strongMonEq I w b a
strongMonEqsym I {w} {a} {b} (n , c1 , c2) = (n , c2 , c1)

inOpenBarstrongMonEqsym : (I : Inh) {w : 𝕎·} {a b : CTerm}
                          → inOpenBar I w (λ w' _ → strongMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → strongMonEq I w' b a)
inOpenBarstrongMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , e2 , z) = h w1 e1 in
  (w2 , e2 , λ w3 e3 → strongMonEqsym I (z w3 e3))

weakMonEqsym : (I : Inh) {w : 𝕎·} {a b : CTerm} → weakMonEq I w a b → weakMonEq I w b a
weakMonEqsym I {w} {a} {b} m w1 e1 = let (n , c1 , c2) = m _ e1 in (n , c2 , c1)

inOpenBarweakMonEqsym : (I : Inh) {w : 𝕎·} {a b : CTerm}
                          → inOpenBar I w (λ w' _ → weakMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → weakMonEq I w' b a)
inOpenBarweakMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , e2 , z) = h _ e1 in
   (_ , e2 , λ w3 e3 → weakMonEqsym I (z _ e3))

eqSQUASH : {a b : CTerm} → a ≡ b → SQUASH a ≡ SQUASH b
eqSQUASH {a} {b} e rewrite e = refl

eqAPPLY : {a b c d : CTerm} → a ≡ b → c ≡ d → APPLY a c ≡ APPLY b d
eqAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl

eqLAPPLY : {a b c d : CTerm} → a ≡ b → c ≡ d → LAPPLY a c ≡ LAPPLY b d
eqLAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl

sub-NUM-SQUASH-SUM : (n : ℕ) (p : CTerm) → # p →
                     sub (NUM n) (SQUASH (SUM LNAT (LAPPLY2 p (VAR 2) (VAR 0))))
                     ≡ SQUASH (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0)))
sub-NUM-SQUASH-SUM n p cp rewrite subvNotIn 2 (NUM n) p (cp _)
                                | shiftDownTrivial 2 p (λ w c → cp _) = eqSQUASH refl


sub-LAPPLY2-NUM-VAR : (t p : CTerm) (n : ℕ) → # p → sub t (LAPPLY2 p (NUM n) (VAR 0)) ≡ LAPPLY2 p (NUM n) t
sub-LAPPLY2-NUM-VAR t p n cp rewrite subvNotIn 0 (shiftUp 0 t) p (cp _)
                                   | shiftDownTrivial 0 p (λ w c → cp _)
                                   | shiftDownUp t 0 = eqLAPPLY refl refl

equalInTypesubLAPPLY2 : {u : ℕ} {I : Inh} {w : 𝕎·} {p t a b : CTerm} {n : ℕ}
                       → # p
                       → equalInType u I w (sub0 t (LAPPLY2 p (NUM n) (VAR 0))) a b
                       → equalInType u I w (LAPPLY2 p (NUM n) t) a b
equalInTypesubLAPPLY2 {u} {I} {w} {p} {t} {a} {b} {n} cp e rewrite sub-LAPPLY2-NUM-VAR t p n cp = e

#APPLY2-NUM : (p m : CTerm) (n : ℕ) → # p → # m → # APPLY2 p (NUM n) m
#APPLY2-NUM p m n cp cm v i rewrite ++[] (fvars p) with ∈-++⁻ (fvars p) i
... | inj₁ x = cp _ x
... | inj₂ x = cm _ x


wPredExtIrrFun-allI-equalInType : (u : ℕ) (I1 I2 : Inh) (w : 𝕎·) (T a b : CTerm)
                                  → wPredExtIrr {I1} {w} (λ w1 e1 → allI I2 (λ i → equalInType u i w1 T a b))
wPredExtIrrFun-allI-equalInType u I1 I2 w T a b w' e1 e2 h = h



-- LOWER properties
eqTypesLOWER : (u : ℕ) (I : Inh) (w : 𝕎·) (T a₁ a₂ : CTerm) (wf : wfInh< I)
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


impliesEqualInTypeLower : (u : ℕ) (I : Inh) (w : 𝕎·) (T a₁ a₂ : CTerm)
                          → ∀𝕎 I w (λ w' _ → allI (lower I) (λ i → equalInType u i w' T a₁ a₂))
                          → equalInType u I w (LOWER T) a₁ a₂
impliesEqualInTypeLower u I w T a₁ a₂ e =
  let e' : ∀𝕎 I w (λ w' _ → allI (lower I) (λ i → eqTypes (uni u) i w' T T))
      e' = (λ w1 e1 i c₁ c₂ k c₃ c₄ → let (eqt , eqi) = e w1 e1 i c₁ c₂ k c₃ c₄ in eqt) in
   (EQTLOWER T T (compAllRefl I (LOWER T) w) (compAllRefl I (LOWER T) w) e' ,
    ∀𝕎impliesinOpenBar {I} {w} λ w1 e1 i c₁ c₂ k c₃ c₄ → proj₂ (e w1 e1 i c₁ c₂ k c₃ c₄))


equalInTypeLower : (u : ℕ) (I : Inh) (w : 𝕎·) (T a₁ a₂ : CTerm)
                   → equalInType u I w (LOWER T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → allI (lower I) (λ i → equalInType u i w1 T a₁ a₂))
equalInTypeLower u I w T a₁ a₂ (EQTNAT x x₁ , eqi) = ⊥-elim (LOWERneqNAT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (LOWERneqQNAT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LOWERneqLT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LOWERneqQLT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTFREE x x₁ , eqi) = ⊥-elim (LOWERneqFREE (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LOWERneqPI (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LOWERneqSUM (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LOWERneqSET (compAllVal I x₁ tt))
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
eqTypesSHRINK : (u : ℕ) (I : Inh) (w : 𝕎·) (T a₁ a₂ : CTerm) (wf : wfInh< I)
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

impliesEqualInTypeShrink : (u : ℕ) (I : Inh) (w : 𝕎·) (T a₁ a₂ : CTerm)
                          → ∀𝕎 I w (λ w' _ → allI (shrink I) (λ i → equalInType u i w' T a₁ a₂))
                          → equalInType u I w (SHRINK T) a₁ a₂
impliesEqualInTypeShrink u I w T a₁ a₂ e =
  let e' : ∀𝕎 I w (λ w' _ → allI (shrink I) (λ i → eqTypes (uni u) i w' T T))
      e' = (λ w1 e1 i c₁ c₂ k c₃ c₄ → let (eqt , eqi) = e w1 e1 i c₁ c₂ k c₃ c₄ in eqt) in
   (EQTSHRINK T T (compAllRefl I (SHRINK T) w) (compAllRefl I (SHRINK T) w) e' ,
    ∀𝕎impliesinOpenBar {I} {w} λ w1 e1 i c₁ c₂ k c₃ c₄ → proj₂ (e w1 e1 i c₁ c₂ k c₃ c₄))

equalInTypeShrink : (u : ℕ) (I : Inh) (w : 𝕎·) (T a₁ a₂ : CTerm)
                   → equalInType u I w (SHRINK T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → allI (shrink I) (λ i → equalInType u i w1 T a₁ a₂))
equalInTypeShrink u I w T a₁ a₂ (EQTNAT x x₁ , eqi) = ⊥-elim (SHRINKneqNAT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (SHRINKneqQNAT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SHRINKneqLT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SHRINKneqQLT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTFREE x x₁ , eqi) = ⊥-elim (SHRINKneqFREE (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SHRINKneqPI (compAllVal I x₁ tt))
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


allI-equalInType : (u : ℕ) (I : Inh) (wf : wfInh≤ I) (w : 𝕎·) (T a b : CTerm)
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


inhL-pred : (u i j m i0 : ℕ) (c : i0 ≤ pred i) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : 𝕎·) (T : CTerm)
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


inh-f-inhN2Ls : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : 𝕎·) (T : CTerm)
                → Σ Term (λ t → equalInType u (inhN u (suc j) (pred i)) w T t t)
                → Inh.f (inhN2Ls u j) (Inh.m (inhN2Ls u j)) i c₂ w T
inh-f-inhN2Ls u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls u j i c₁ c₂ w T h | inj₂ p rewrite p = h


inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
                     (k : ℕ) (c₃ : j ≤ k) (c₄ : k ≤ pred i)
                     (w : 𝕎·) (T : CTerm)
                     → Σ Term (λ t → equalInType u (inhN u k (pred i)) w T t t)
                     → Inh.f (inhN2Ls u j) k i c₂ w T
inh-f-inhN2Ls-pred u j i c₁ c₂ k c₃ c₄ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls-pred u j i c₁ c₂ k c₃ c₄ w T h | inj₂ p rewrite p = h


if-inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : 𝕎·) (T : CTerm)
                        → Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) i c₂ w T
                        → Σ Term (λ t → equalInType u (inhN u j (pred i)) w T t t)
if-inh-f-inhN2Ls-pred u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls-pred u j i c₁ c₂ w T h | inj₂ p rewrite p = h


allI-inhN2Ls-ΣequalInType : (u j i : ℕ) (w : 𝕎·) (t : CTerm) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
                            → allIW (inhN2Ls u j) (λ i → i w t)
                            → Σ Term (λ z → equalInType u (inhN u j i) w t z z)
allI-inhN2Ls-ΣequalInType u j i w t c₁ c₂ h =
  if-inh-f-inhN2Ls-pred
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) j ≤-refl c₁)


if-inh-f-inhN2Ls-pred2 : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
                         (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
                         (w : 𝕎·) (T : CTerm)
                         → Inh.f (inhN2Ls u j) k i c₂ w T
                         → Σ Term (λ t → equalInType u (inhN u k (pred i)) w T t t)
if-inh-f-inhN2Ls-pred2 u j i c₁ c₂ k c₃ c₄ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls-pred2 u j i c₁ c₂ k c₃ c₄ w T h | inj₂ p rewrite p = h


allI-inhN2Ls-ΣequalInType2 : (u j i : ℕ) (w : 𝕎·) (t : CTerm) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
                             (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
                            → allIW (inhN2Ls u j) (λ i → i w t)
                            → Σ Term (λ z → equalInType u (inhN u k i) w t z z)
allI-inhN2Ls-ΣequalInType2 u j i w t c₁ c₂ k c₃ c₄ h =
  if-inh-f-inhN2Ls-pred2
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) k c₃ (≤-trans c₄ (n≤1+n _)) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) k (≤-trans (n≤1+n _) c₃) c₄)


mkinh2L≡inhNaux : (u j i : ℕ) (c₁ : j ≤ i) (c₂ : i ≤ suc j) (m z : ℕ) (c : z ≤ i) (w : 𝕎·) (t : CTerm)
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
    h : (m z : ℕ) (c : z ≤ i) (w : 𝕎·) (t : CTerm)
        → Inh.f (inhN2L u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
    h m z c w t = mkinh2L≡inhNaux u j i c₁ c₂ m z c w t


mkinh1Ls≡inhNaux : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j) (m z : ℕ) (c : z ≤ i) (w : 𝕎·) (t : CTerm)
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
    h : (m z : ℕ) (c : z ≤ i) (w : 𝕎·) (t : CTerm)
        → Inh.f (inhN1Ls u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
    h m z c w t = mkinh1Ls≡inhNaux u j i c₁ c₂ m z c w t


{--
if-inh-f-inhN2Ls : (u j : ℕ) (w : 𝕎·) (T : CTerm)
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


allI-inhN2Ls-ΣequalInType1Ls : (u j i : ℕ) (w : 𝕎·) (t : CTerm) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j)
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
    e2 : (w : 𝕎·) (T : CTerm) → Inh.f (inhN1Ls u j) k i ci₂ w T ≡ Inh.f (inhN2Ls u j) k i (≤-trans ci₂ (n≤1+n (Inh.n (inhN1Ls u j)))) w T
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


[]≽-inhN2Ls-[]≽-inhN1Ls : {w2 w1 : 𝕎·} {u j : ℕ}
                     → [ inhN2Ls u j ] w2 ⪰ w1
                     → [ inhN1Ls u j ] w2 ⪰ w1
[]≽-inhN2Ls-[]≽-inhN1Ls {w2} {.w2} {u} {j} (⊑-refl· .w2) = ⊑-refl· w2
[]≽-inhN2Ls-[]≽-inhN1Ls {w2} {w1} {u} {j} (extTrans h h₁) = extTrans ([]≽-inhN2Ls-[]≽-inhN1Ls h) ([]≽-inhN2Ls-[]≽-inhN1Ls h₁)
[]≽-inhN2Ls-[]≽-inhN1Ls {.(w1 ++ choice name t ∷ [])} {w1} {u} {j} (extChoice .w1 name l t res x x₁) =
  extChoice w1 name l t res x (allI-inhN2Ls-allI-inh1Ls {u} {j} {λ i → i w1 (res (length l) t)} x₁)
[]≽-inhN2Ls-[]≽-inhN1Ls {.(w1 ++ start name res ∷ [])} {w1} {u} {j} (extEntry .w1 name res x) =
  extEntry w1 name res x


[]≽-inhN2Ls-to-N1s : {w2 w1 : 𝕎·} {u j i k : ℕ} → suc j ≤ i → i ≤ suc j → suc j ≤ k → k ≤ i
                     → [ inhN2Ls u j ] w2 ⪰ w1
                     → [ inhN u k i ] w2 ⪰ w1
[]≽-inhN2Ls-to-N1s {w2} {w1} {u} {j} {i} {k} a b c d h rewrite inhN≡inhN1Ls {u} {j} {i} {k} a b c d =
  []≽-inhN2Ls-[]≽-inhN1Ls h


{--then-lower : (w : 𝕎·) (a b : CTerm) → eqintype w NAT a b → eqintype w (LOWER NAT) a b
then-lower w a b (u , n , k , e) =
  (u , suc n , k , λ j c →
   impliesEqualInTypeLower u (inhN u j (k + j)) w NAT a b λ w1 e1 → {!!})

if-lower : (w : 𝕎·) (a b : CTerm) → eqintype w (LOWER NAT) a b → eqintype w NAT a b
if-lower w a b (u , n , k , e) = (u , n , k , λ j c → {!!})--}
--}
\end{code}
