\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module classical (bar : Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
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
open import Induction.WellFounded
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
open import mod


--module props2 (bar : Bar) where
module props2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(E)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_ttrunc(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_tconst(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_subsing(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar) -- this is the one where a function is not recognized as terminating, but does not break the bar abstraction
-- open import type_sys_props_nat (bar)
-- open import type_sys_props_qnat (bar)
-- open import type_sys_props_lt (bar)
-- open import type_sys_props_qlt (bar)
-- open import type_sys_props_free (bar)
-- open import type_sys_props_pi (bar)
-- open import type_sys_props_sum (bar)
-- open import type_sys_props_set (bar)
-- open import type_sys_props_eq (bar)
-- open import type_sys_props_union (bar)
-- open import type_sys_props_tsquash (bar)
-- open import type_sys_props_ffdefs (bar)
-- open import props1 (bar)
-- open import terms (bar)
\end{code}




\begin{code}[hide]
eqInType-extl1 : {i : ℕ} {w : 𝕎·} {A : CTerm}
                 (B C : CTerm)
                 (eqa1 : equalTypes i w A B) (eqa2 : equalTypes i w A C)
                 {a₁ a₂ : CTerm}
                 → eqInType (uni i) w eqa1 a₁ a₂
                 → eqInType (uni i) w eqa2 a₁ a₂
eqInType-extl1 {i} {w} {A} B C eqa1 eqa2 {a₁} {a₂} ei =
  TSP.extl1 (typeSysConds i w A B eqa1)
            C eqa2 a₁ a₂ ei


eqInType-extr1 : {i : ℕ} {w : 𝕎·} {A : CTerm}
                 (B C : CTerm)
                 (eqa1 : equalTypes i w A B) (eqa2 : equalTypes i w C B)
                 {a₁ a₂ : CTerm}
                 → eqInType (uni i) w eqa1 a₁ a₂
                 → eqInType (uni i) w eqa2 a₁ a₂
eqInType-extr1 {i} {w} {A} B C eqa1 eqa2 {a₁} {a₂} ei =
  TSP.extr1 (typeSysConds i w A B eqa1)
            C eqa2 a₁ a₂ ei

eqInType-sym : {i : ℕ} {w : 𝕎·} {A B : CTerm}
               (eqa : equalTypes i w A B)
               {a₁ a₂ : CTerm}
               → eqInType (uni i) w eqa a₁ a₂
               → eqInType (uni i) w eqa a₂ a₁
eqInType-sym {i} {w} {A} {B} eqa {a₁} {a₂} ei = TSP.isym (typeSysConds i w A B eqa) a₁ a₂ ei


wPredExtIrr-eqInType : {i : ℕ} {w : 𝕎·} {A B : CTerm}
                       (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A B))
                       (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType (uni i) w₁ (eqta w₁ e) a b)
wPredExtIrr-eqInType {i} {w} {A} {B} eqta a b w' e1 e2 h =
  eqInType-extl1 B B (eqta w' e1) (eqta w' e2) h


wPredDepExtIrr-eqInType : {i : ℕ} {w : 𝕎·} {A : CTerm} {B D : CTerm0}
                          (eqtb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D)))
                          (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType {i} {w} {A} {B} {D} eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub0 b D) (sub0 b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


wPredDepExtIrr-eqInType2 : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                           (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A C))
                           (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D)))
                           (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub0 b D) (sub0 b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h



equalInTypeFam→eqTypesFam : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                             (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A C))
                             (eqtb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D)))
                             → ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D))
equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb w1 e1 a₁ a₂ ea =
  eqtb w1 e1 a₁ a₂ (eqa , eqInType-extl1 C A (eqta w1 e1) eqa ea)
  where
    eqa : equalTypes i w1 A A
    eqa = TEQrefl-equalTypes i w1 A C (eqta w1 e1)



eqTypesSET← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#SET A B) (#SET C D)
eqTypesSET← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTSET A B C D (#compAllRefl (#SET A B) w) (#compAllRefl (#SET C D) w)
        eqta
        (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb)
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb))



eqTypesSUM← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#SUM A B) (#SUM C D)
eqTypesSUM← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTSUM A B C D (#compAllRefl (#SUM A B) w) (#compAllRefl (#SUM C D) w)
        eqta
        (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb)
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb))



eqTypesPI← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#PI A B) (#PI C D)
eqTypesPI← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTPI A B C D (#compAllRefl (#PI A B) w) (#compAllRefl (#PI C D) w)
        eqta
        (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb)
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb))



eqTypesFUN← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → equalTypes i w A C
               → equalTypes i w B D
               → equalTypes i w (#FUN A B) (#FUN C D)
eqTypesFUN← {w} {i} {A} {B} {C} {D} eqta eqtb rewrite #FUN≡#PI A B | #FUN≡#PI C D =
  eqTypesPI← (eqTypes-mon (uni i) eqta) eqb
    where
      eqb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ D ⌟))
      eqb w1 e1 a₁ a₂ eqa rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ D = eqTypes-mon (uni i) eqtb w1 e1


eqInTypeExtL1-true : {i : ℕ} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes (uni i) w A B)
                     → eqInTypeExtL1 eqt
eqInTypeExtL1-true {i} {w} {A} {B} eqt = TSP.extl1 (typeSysConds i w A B eqt)



eqInType→equalInType : {u : ℕ} {w : 𝕎·} {A A1 A2 a₁ a₂ : CTerm}
                        → A ≡ A1
                        → (eqt : equalTypes u w A1 A2)
                        → equalTerms u w eqt a₁ a₂
                        → equalInType u w A a₁ a₂
eqInType→equalInType {u} {w} {A} {A1} {A2} {a₁} {a₂} e eqt eqi rewrite e =
  TEQrefl-equalTypes u w A1 A2 eqt ,
  eqInTypeExtL1-true eqt A1 (TEQrefl-equalTypes u w A1 A2 eqt) a₁ a₂ eqi



equalInType→eqInType : {u : ℕ} {w : 𝕎·} {A A1 A2 a₁ a₂ : CTerm}
                        → A ≡ A1
                        → {eqt : equalTypes u w A1 A2}
                        → equalInType u w A a₁ a₂
                        → equalTerms u w eqt a₁ a₂
equalInType→eqInType {u} {w} {A} {A1} {A2} {a₁} {a₂} e {eqt} eqi rewrite e =
  eqInTypeExtL1-true {u} (fst eqi) A2 eqt a₁ a₂ (snd eqi)



∀𝕎-equalInType→eqInType : {i : ℕ} {w : 𝕎·} {A B a b : CTerm}
                        (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A B))
                        → ∀𝕎 w (λ w' e → equalInType i w' A a b)
                        → ∀𝕎 w (λ w' e → eqInType (uni i) w' (eqta w' e) a b)
∀𝕎-equalInType→eqInType {i} {w} {A} {B} {a} {b} eqta eqi w1 e1 =
  equalInType→eqInType refl {eqta w1 e1} (eqi w1 e1)



equalInType-mon : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                  → equalInType u w T a b
                  → ∀𝕎 w (λ w' _ → equalInType u w' T a b)
equalInType-mon {u} {w} {T} {a} {b} (eqt , eqi) w' e =
  eqTypes-mon (uni u) eqt w' e ,
  eqInType-mon (is-uni-uni u) e eqt (eqTypes-mon (uni u) eqt w' e) a b eqi



equalInType-refl : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                   → equalInType u w T a b
                   → equalInType u w T a a
equalInType-refl {u} {w} {T} {a} {b} eqi =
  EQTtrans-equalInType u w T a b a eqi (EQTsym-equalInType u w T a b eqi)



equalInType-sym : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                  → equalInType u w T a b
                  → equalInType u w T b a
equalInType-sym {u} {w} {T} {a} {b} eqi = EQTsym-equalInType u w T a b eqi



eqTypesEQ← : {w : 𝕎·} {i : ℕ} {a1 a2 b1 b2 A B : CTerm}
               → equalTypes i w A B
               → equalInType i w A a1 b1
               → equalInType i w A a2 b2
               → equalTypes i w (#EQ a1 a2 A) (#EQ b1 b2 B)
eqTypesEQ← {w} {i} {a1} {a2} {b1} {b2} {A} {B} eqtA eqt1 eqt2 =
  EQTEQ a1 b1 a2 b2 A B (#compAllRefl (#EQ a1 a2 A) w) (#compAllRefl (#EQ b1 b2 B) w)
        (eqTypes-mon (uni i) eqtA) (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtA))
        (∀𝕎-equalInType→eqInType (eqTypes-mon (uni i) eqtA) (equalInType-mon eqt1))
        (∀𝕎-equalInType→eqInType (eqTypes-mon (uni i) eqtA) (equalInType-mon eqt2))


eqTypesFUN→₁ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → equalTypes i w (#FUN A B) (#FUN C D)
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
{-# TERMINATING #-}
--{-# INLINE ∀𝕎-inOpenBarFunc #-}
--{-# INLINE ↑inOpenBar #-}
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTNAT x x₁) = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTQNAT x x₁) = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (PIneqLT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTFREE x x₁) = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
  rewrite #FUN/PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)
        | #FUN/PIinj2 {A} {B} {A1} {B1} (#compAllVal x tt)
        | #FUN/PIinj1 {C} {D} {A2} {B2} (#compAllVal x₁ tt)
        | #FUN/PIinj2 {C} {D} {A2} {B2} (#compAllVal x₁ tt)
  = eqta

eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (PIneqSET (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (PIneqTUNION (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (PIneqQTUNION (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSQUASH A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTTRUNC A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqTTRUNC (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTCONST A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqTCONST (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSUBSING A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqSUBSING (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTUNIV m p c₁ c₂) = ⊥-elim (PIneqUNIV (compAllVal c₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTLIFT A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTBAR x) w' e' =
  EQTBAR (Mod.∀𝕎-□Func M aw (Mod.↑□ M x e'))
-- (a) This does not work
-- EQTBAR (∀𝕎-inOpenBarFunc aw (↑inOpenBar x e'))
-- (b) Unfolding and reducing works though:
-- EQTBAR (λ w1 e1 → fst (x w1 (⊑-trans· e' e1)) ,
--                     fst (snd (x w1 (⊑-trans· e' e1))) ,
--                     λ w3 e3 z → aw w3 z (snd (snd (x w1 (⊑-trans· e' e1))) w3 e3 (⊑-trans· e' z)))
  where
    aw : ∀𝕎 w' (λ w1 e1 → eqTypes (uni i) w1 (#FUN A B) (#FUN C D) → equalTypes i w1 A C)
    aw w1 e1 eqt = eqTypesFUN→₁ eqt w1 (⊑-refl· w1)



eqTypesNEG→ : {w : 𝕎·} {i : ℕ} {A B : CTerm}
               → equalTypes i w (#NEG A) (#NEG B)
               → equalTypes i w A B
eqTypesNEG→ {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B = eqTypesFUN→₁ eqt w (⊑-refl· w)


eqTypesNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #NAT #NAT
eqTypesNAT {w} {i} = EQTNAT (#compAllRefl #NAT w) (#compAllRefl #NAT w)


eqTypesQNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #QNAT #QNAT
eqTypesQNAT {w} {i} = EQTQNAT (#compAllRefl #QNAT w) (#compAllRefl #QNAT w)



eqTypesTSQUASH← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                   → equalTypes i w A B
                   → equalTypes i w (#TSQUASH A) (#TSQUASH B)
eqTypesTSQUASH← {w} {i} {A} {B} eqtA =
  EQTSQUASH
    A B
    (#compAllRefl (#TSQUASH A) w)
    (#compAllRefl (#TSQUASH B) w)
    (eqTypes-mon (uni i) eqtA)
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtA))


eqTypesTTRUNC← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                   → equalTypes i w A B
                   → equalTypes i w (#TTRUNC A) (#TTRUNC B)
eqTypesTTRUNC← {w} {i} {A} {B} eqtA =
  EQTTRUNC
    A B
    (#compAllRefl (#TTRUNC A) w)
    (#compAllRefl (#TTRUNC B) w)
    (eqTypes-mon (uni i) eqtA)
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtA))



eqTypesTCONST← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w (#TCONST A) (#TCONST B)
eqTypesTCONST← {w} {i} {A} {B} eqtA =
  EQTCONST
    A B
    (#compAllRefl (#TCONST A) w)
    (#compAllRefl (#TCONST B) w)
    (eqTypes-mon (uni i) eqtA)
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtA))



eqTypesSUBSING← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w (#SUBSING A) (#SUBSING B)
eqTypesSUBSING← {w} {i} {A} {B} eqtA =
  EQTSUBSING
    A B
    (#compAllRefl (#SUBSING A) w)
    (#compAllRefl (#SUBSING B) w)
    (eqTypes-mon (uni i) eqtA)
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtA))



eqTypes-local : {u : univs} {w : 𝕎·} {A B : CTerm}
                → □· w (λ w' _ → eqTypes u w' A B)
                → eqTypes u w A B
eqTypes-local {u} {w} {A} {B} i =
  EQTBAR i


TSQUASH-eq→isType : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                    → TSQUASH-eq (equalInType i w A) w a b
                    → isType i w A
TSQUASH-eq→isType {w} {i} {a} {b} {A} (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) = fst ea
TSQUASH-eq→isType {w} {i} {a} {b} {A} (TSQUASH-eq-trans t h1 h2) = TSQUASH-eq→isType h1



TSQUASHeq→isType : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                    → TSQUASHeq (equalInType i w A) w a b
                    → isType i w A
TSQUASHeq→isType {w} {i} {a} {b} {A} h = TSQUASH-eq→isType (→TSQUASH-eq h)


□·-TSQUASHeq→isType : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                          → □· w (λ w' _ → TSQUASHeq (equalInType i w' A) w' a b)
                          → isType i w A
□·-TSQUASHeq→isType {w} {i} {a} {b} {A} j =
  eqTypes-local (Mod.∀𝕎-□Func M aw j)
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalInType i w' A) w' a b → eqTypes (uni i) w' A A)
    aw w1 e1 h = TSQUASHeq→isType h
-- (c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) = fst ea


equalInTypeTSQUASH← : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                       → □· w (λ w' _ → TSQUASHeq (equalInType i w' A) w' a b)
                       → equalInType i w (#TSQUASH A) a b
equalInTypeTSQUASH← {w} {i} {a} {b} {A} j =
  eqTypesTSQUASH← (□·-TSQUASHeq→isType {w} {i} {a} {b} {A} j) ,
  Mod.∀𝕎-□Func M aw j
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalInType i w' A) w' a b
                        → TSQUASHeq (equalTerms i w' (eqTypes-mon (uni i) (□·-TSQUASHeq→isType {w} {i} {a} {b} {A} j) w' e')) w' a b)
    aw w1 e1 h = TSQUASHeq-ext-eq (λ a1 a2 ea → equalInType→eqInType refl {eqTypes-mon (uni i) (□·-TSQUASHeq→isType {_} {i} {a} {b} j) w1 e1} ea) h
{--(c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni i) (□·-TSQUASHeq→isType {_} {i} {a} {b} j) w1 e1} ea
--}




TTRUNC-eq→isType : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                    → TTRUNC-eq (equalInType i w A) w a b
                    → isType i w A
TTRUNC-eq→isType {w} {i} {a} {b} {A} (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) = fst ea
TTRUNC-eq→isType {w} {i} {a} {b} {A} (TTRUNC-eq-trans t h1 h2) = TTRUNC-eq→isType h1



TTRUNCeq→isType : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                    → TTRUNCeq (equalInType i w A) w a b
                    → isType i w A
TTRUNCeq→isType {w} {i} {a} {b} {A} h = TTRUNC-eq→isType (→TTRUNC-eq h)


□·-TTRUNCeq→isType : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                          → □· w (λ w' _ → TTRUNCeq (equalInType i w' A) w' a b)
                          → isType i w A
□·-TTRUNCeq→isType {w} {i} {a} {b} {A} j =
  eqTypes-local (Mod.∀𝕎-□Func M aw j)
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalInType i w' A) w' a b → eqTypes (uni i) w' A A)
    aw w1 e1 h = TTRUNCeq→isType h
-- (c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) = fst ea


equalInTypeTTRUNC← : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                       → □· w (λ w' _ → TTRUNCeq (equalInType i w' A) w' a b)
                       → equalInType i w (#TTRUNC A) a b
equalInTypeTTRUNC← {w} {i} {a} {b} {A} j =
  eqTypesTTRUNC← (□·-TTRUNCeq→isType {w} {i} {a} {b} {A} j) ,
  Mod.∀𝕎-□Func M aw j
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalInType i w' A) w' a b
                        → TTRUNCeq (equalTerms i w' (eqTypes-mon (uni i) (□·-TTRUNCeq→isType {w} {i} {a} {b} {A} j) w' e')) w' a b)
    aw w1 e1 h = TTRUNCeq-ext-eq (λ a1 a2 ea → equalInType→eqInType refl {eqTypes-mon (uni i) (□·-TTRUNCeq→isType {_} {i} {a} {b} j) w1 e1} ea) h



eqTypesQTNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #QTNAT #QTNAT
eqTypesQTNAT {w} {i} = eqTypesTSQUASH← eqTypesNAT



□·-#strongMonEq-#NUM : (k : ℕ) (w : 𝕎·) → □· w (λ w' _ → #strongMonEq w' (#NUM k) (#NUM k))
□·-#strongMonEq-#NUM k w = Mod.∀𝕎-□ M (λ w2 e2 → #strongMonEq-#NUM w2 k)




≡CTerm→eqTypes : {u : univs} {w : 𝕎·} {A B C D : CTerm}
                  → A ≡ C
                  → B ≡ D
                  → eqTypes u w A B
                  → eqTypes u w C D
≡CTerm→eqTypes {u} {w} {A} {B} {C} {D} e f z rewrite e | f = z


≡CTerm→equalInType : {u : ℕ} {w : 𝕎·} {A B a b : CTerm}
                      → A ≡ B
                      → equalInType u w A a b
                      → equalInType u w B a b
≡CTerm→equalInType {u} {w} {A} {B} {a} {b} e z rewrite e = z



NUM-equalInType-NAT : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #NAT (#NUM k) (#NUM k)
NUM-equalInType-NAT i w k = eqTypesNAT , Mod.∀𝕎-□ M (λ w' e' → #strongMonEq-#NUM w' k)


isTypeNAT! : {w : 𝕎·} {i : ℕ} → isType i w #NAT!
isTypeNAT! {w} {i} = eqTypesTCONST← eqTypesNAT


NUM-equalInType-NAT! : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #NAT! (#NUM k) (#NUM k)
NUM-equalInType-NAT! i w k =
  isTypeNAT! ,
  Mod.∀𝕎-□ M (λ w' e' → Mod.∀𝕎-□ M (λ w'' e'' → #strongMonEq-#NUM w'' k) , #⇓→#⇓!-NUM w' k , #⇓→#⇓!-NUM w' k)


equalInTypeTSQUASH→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                       → equalInType i w (#TSQUASH A) a b
                       → □· w (λ w' _ → TSQUASHeq (equalInType i w' A) w' a b)
{-# TERMINATING #-}
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTNAT x x₁ , eqi) = ⊥-elim (TSQUASHneqNAT (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTQNAT x x₁ , eqi) = ⊥-elim (TSQUASHneqQNAT (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (TSQUASHneqLT (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (TSQUASHneqQLT (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTFREE x x₁ , eqi) = ⊥-elim (TSQUASHneqFREE (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TSQUASHneqPI (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TSQUASHneqSUM (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TSQUASHneqSET (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TSQUASHneqTUNION (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (TSQUASHneqEQ (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (TSQUASHneqUNION (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (TSQUASHneqQTUNION (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a b → TSQUASHeq (equalInType i w' A) w' a b)
    aw w1 e1 p = TSQUASHeq-ext-eq (λ a1 a2 ea → eqInType→equalInType (#TSQUASHinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
--(c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) =
--      c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , eqInType→equalInType (#TSQUASHinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TSQUASHneqTTRUNC (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TSQUASHneqTCONST (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TSQUASHneqSUBSING (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (TSQUASHneqFFDEFS (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (TSQUASHneqUNIV (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TSQUASHneqLIFT (compAllVal x₁ tt))
equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType i w' (#TSQUASH A))
                        → equalTerms i w' z a b
                        → □· w' (↑wPred' (λ w'' e → TSQUASHeq (equalInType i w'' A) w'' a b) e'))
    aw w1 e1 z h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (equalInTypeTSQUASH→ (z , h))




equalInTypeTTRUNC→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                       → equalInType i w (#TTRUNC A) a b
                       → □· w (λ w' _ → TTRUNCeq (equalInType i w' A) w' a b)
{-# TERMINATING #-}
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTNAT x x₁ , eqi) = ⊥-elim (TTRUNCneqNAT (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTQNAT x x₁ , eqi) = ⊥-elim (TTRUNCneqQNAT (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (TTRUNCneqLT (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (TTRUNCneqQLT (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTFREE x x₁ , eqi) = ⊥-elim (TTRUNCneqFREE (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TTRUNCneqPI (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TTRUNCneqSUM (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TTRUNCneqSET (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TTRUNCneqTUNION (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (TTRUNCneqEQ (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (TTRUNCneqUNION (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (TTRUNCneqQTUNION (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TTRUNCneqTSQUASH (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' a b → TTRUNCeq (equalInType i w' A) w' a b)
    aw w1 e1 p = TTRUNCeq-ext-eq (λ a1 a2 ea → eqInType→equalInType (#TTRUNCinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
--(c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) =
--      c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , eqInType→equalInType (#TTRUNCinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TTRUNCneqTCONST (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TTRUNCneqSUBSING (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (TTRUNCneqFFDEFS (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (TTRUNCneqUNIV (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TTRUNCneqLIFT (compAllVal x₁ tt))
equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType i w' (#TTRUNC A))
                        → equalTerms i w' z a b
                        → □· w' (↑wPred' (λ w'' e → TTRUNCeq (equalInType i w'' A) w'' a b) e'))
    aw w1 e1 z h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (equalInTypeTTRUNC→ (z , h))



equalInType-NAT→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → equalInType i w #NAT a b
                    → □· w (λ w' _ → NATeq w' a b)
equalInType-NAT→ i w a b (eqt , eqi) =
  eqInType-⇛-NAT (uni i) w #NAT #NAT a b (#compAllRefl #NAT w) (#compAllRefl #NAT w) eqt eqi




TSQUASH-eq-NAT→weakMonEq : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                            → TSQUASH-eq (equalInType i w #NAT) w a b
                            → Lift (lsuc L) (⇓sameℕ w ⌜ a ⌝ ⌜ b ⌝)
TSQUASH-eq-NAT→weakMonEq i w a b (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  Mod.□-const M (Mod.∀𝕎-□Func M aw j)
  where
    j : □· w (λ w' _ → NATeq w' a1 a2)
    j = equalInType-NAT→ i w a1 a2 ea

    aw : ∀𝕎 w (λ w1 e1 → NATeq w1 a1 a2 → Lift (lsuc L) (⇓sameℕ w ⌜ a ⌝ ⌜ b ⌝))
    aw w1 e1 (n , c₁' , c₂') = lift (n , ∼C!→#⇓ {w} {a} {#NUM n} tt c₁'' ,  ∼C!→#⇓ {w} {b} {#NUM n} tt c₂'')
      where
        c₁'' : ∼C! w a (#NUM n)
        c₁'' = ≡R→∼C! {w} {a} {a1} {#NUM n} (#⇛→≡ c₁' i1) c1

        c₂'' : ∼C! w b (#NUM n)
        c₂'' = ≡R→∼C! {w} {b} {a2} {#NUM n} (#⇛→≡ c₂' i2) c2
TSQUASH-eq-NAT→weakMonEq i w a b (TSQUASH-eq-trans t h1 h2) =
  lift-⇓sameℕ-trans (TSQUASH-eq-NAT→weakMonEq i w a t h1) (TSQUASH-eq-NAT→weakMonEq i w t b h2)



equalInType-QTNAT→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #QTNAT a b
                      → □· w (λ w' _ → #weakMonEq w' a b)
equalInType-QTNAT→ i w a b eqi =
  Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqj) --Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqj)
  where
    eqj : □· w (λ w' _ → TSQUASHeq (equalInType i w' #NAT) w' a b)
    eqj = equalInTypeTSQUASH→ {w} {i} {a} {b} {#NAT} eqi

    aw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (↑wPred (λ w'' e → TSQUASHeq (equalInType i w'' #NAT) w'' a b) e')
                        → #weakMonEq w' a b)
    aw w1 e1 h w2 e2 = TSQUASH-eq-NAT→weakMonEq i w2 a b (→TSQUASH-eq (h w2 e2))




equalInTypeTCONST→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                       → equalInType i w (#TCONST A) a b
                       → □· w (λ w' _ → TCONSTeq (equalInType i w' A) w' a b)
{-# TERMINATING #-}
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTNAT x x₁ , eqi) = ⊥-elim (TCONSTneqNAT (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTQNAT x x₁ , eqi) = ⊥-elim (TCONSTneqQNAT (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (TCONSTneqLT (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (TCONSTneqQLT (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTFREE x x₁ , eqi) = ⊥-elim (TCONSTneqFREE (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TCONSTneqPI (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TCONSTneqSUM (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TCONSTneqSET (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (TCONSTneqTUNION (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (TCONSTneqEQ (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (TCONSTneqUNION (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (TCONSTneqQTUNION (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TCONSTneqTSQUASH (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TCONSTneqTTRUNC (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms i w' (eqtA w' e')) w' a b → TCONSTeq (equalInType i w' A) w' a b)
    aw w1 e1 p = TCONSTeq-ext-eq (λ a1 a2 ea → eqInType→equalInType {_} {_} {_} {_} {_} {a1} {a2} (#TCONSTinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TCONSTneqSUBSING (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (TCONSTneqFFDEFS (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (TCONSTneqUNIV (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (TCONSTneqLIFT (compAllVal x₁ tt))
equalInTypeTCONST→ {w} {i} {a} {b} {A} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType i w' (#TCONST A))
                        → equalTerms i w' z a b
                        → □· w' (↑wPred' (λ w'' e → TCONSTeq (equalInType i w'' A) w'' a b) e'))
    aw w1 e1 z h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (equalInTypeTCONST→ (z , h))



equalInTypeSUBSING→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                       → equalInType i w (#SUBSING A) a b
                       → □· w (λ w' _ → SUBSINGeq (equalInType i w' A) a b)
{-# TERMINATING #-}
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTNAT x x₁ , eqi) = ⊥-elim (SUBSINGneqNAT (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTQNAT x x₁ , eqi) = ⊥-elim (SUBSINGneqQNAT (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SUBSINGneqLT (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SUBSINGneqQLT (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTFREE x x₁ , eqi) = ⊥-elim (SUBSINGneqFREE (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUBSINGneqPI (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUBSINGneqSUM (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUBSINGneqSET (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUBSINGneqTUNION (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (SUBSINGneqEQ (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (SUBSINGneqUNION (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (SUBSINGneqQTUNION (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUBSINGneqTSQUASH (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUBSINGneqTTRUNC (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUBSINGneqTCONST (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalTerms i w' (eqtA w' e')) a b → SUBSINGeq (equalInType i w' A) a b)
    aw w1 e1 p = SUBSINGeq-ext-eq (λ a1 a2 ea → eqInType→equalInType {_} {_} {_} {_} {_} {a1} {a2} (#SUBSINGinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (SUBSINGneqFFDEFS (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (SUBSINGneqUNIV (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUBSINGneqLIFT (compAllVal x₁ tt))
equalInTypeSUBSING→ {w} {i} {a} {b} {A} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType i w' (#SUBSING A))
                        → equalTerms i w' z a b
                        → □· w' (↑wPred' (λ w'' e → SUBSINGeq (equalInType i w'' A) a b) e'))
    aw w1 e1 z h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (equalInTypeSUBSING→ (z , h))



TCONSTeq-NAT→weakMonEq : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                          → TCONSTeq (equalInType i w #NAT) w a b
                          → □· w (λ w' _ → #⇛!sameℕ w' a b)
TCONSTeq-NAT→weakMonEq i w a b (h , c₁ , c₂) =
  Mod.∀𝕎-□Func M (λ w1 e1 z → #strongMonEq→#⇛!sameℕ {w1} {a} {b} (∀𝕎-mon e1 c₁) (∀𝕎-mon e1 c₂) z) j
  where
    j : □· w (λ w' _ → NATeq w' a b)
    j = equalInType-NAT→ i w a b h


equalInType-NAT!→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → equalInType i w #NAT! a b
                    → □· w (λ w' _ → #⇛!sameℕ w' a b)
equalInType-NAT!→ i w a b eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw eqj)
  where
    eqj : □· w (λ w' _ → TCONSTeq (equalInType i w' #NAT) w' a b)
    eqj = equalInTypeTCONST→ {w} {i} {a} {b} {#NAT} eqi

    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalInType i w' #NAT) w' a b
                        → □· w' (↑wPred' (λ w'' _ → #⇛!sameℕ w'' a b) e'))
    aw w1 e1 h = Mod.∀𝕎-□Func M (λ w2 e2 h z → h) (TCONSTeq-NAT→weakMonEq i w1 a b h)



TSQUASH-eq-NAT!→weakMonEq! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                             → TSQUASH-eq (equalInType i w #NAT!) w a b
                             → Lift (lsuc L) (⇓!sameℕ w ⌜ a ⌝ ⌜ b ⌝)
TSQUASH-eq-NAT!→weakMonEq! i w a b (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  Mod.□-const M (Mod.∀𝕎-□Func M aw j)
  where
    j : □· w (λ w' _ → #⇛!sameℕ w' a1 a2)
    j = equalInType-NAT!→ i w a1 a2 ea

    aw : ∀𝕎 w (λ w1 e1 → #⇛!sameℕ w1 a1 a2 → Lift (lsuc L) (⇓!sameℕ w ⌜ a ⌝ ⌜ b ⌝))
    aw w1 e1 (n , c₁' , c₂') = lift (n , ∼C!→#⇓! {w} {a} {#NUM n} tt c₁'' ,  ∼C!→#⇓! {w} {b} {#NUM n} tt c₂'')
      where
        c₁'' : ∼C! w a (#NUM n)
        c₁'' = ≡R→∼C! {w} {a} {a1} {#NUM n} (#⇛!→≡ c₁' i1) c1

        c₂'' : ∼C! w b (#NUM n)
        c₂'' = ≡R→∼C! {w} {b} {a2} {#NUM n} (#⇛!→≡ c₂' i2) c2
TSQUASH-eq-NAT!→weakMonEq! i w a b (TSQUASH-eq-trans t h1 h2) =
  lift-⇓!sameℕ-trans (TSQUASH-eq-NAT!→weakMonEq! i w a t h1) (TSQUASH-eq-NAT!→weakMonEq! i w t b h2)



equalInType-QTNAT!→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #QTNAT! a b
                      → □· w (λ w' _ → #weakMonEq! w' a b)
equalInType-QTNAT!→ i w a b eqi =
  Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqj) --Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqj)
  where
    eqj : □· w (λ w' _ → TSQUASHeq (equalInType i w' #NAT!) w' a b)
    eqj = equalInTypeTSQUASH→ {w} {i} {a} {b} {#NAT!} eqi

    aw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (↑wPred (λ w'' e → TSQUASHeq (equalInType i w'' #NAT!) w'' a b) e')
                        → #weakMonEq! w' a b)
    aw w1 e1 h w2 e2 = TSQUASH-eq-NAT!→weakMonEq! i w2 a b (→TSQUASH-eq (h w2 e2))


#strongMonEq-#N0 : (w : 𝕎·) → #strongMonEq w #N0 #N0
#strongMonEq-#N0 w = #strongMonEq-#NUM w 0


#strongMonEq-#N1 : (w : 𝕎·) → #strongMonEq w #N1 #N1
#strongMonEq-#N1 w = #strongMonEq-#NUM w 1


→equalInType-NAT : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → NATeq w' a b)
                    → equalInType i w #NAT a b
→equalInType-NAT i w a b j = eqTypesNAT , j



→equalInType-QNAT : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #weakMonEq w' a b)
                    → equalInType i w #QNAT a b
→equalInType-QNAT i w a b j = eqTypesQNAT , j



equalInType-QNAT→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #QNAT a b
                     → □· w (λ w' _ → #weakMonEq w' a b)
equalInType-QNAT→ i w a b (eqt , eqi) =
  eqInType-⇛-QNAT (uni i) w #QNAT #QNAT a b (#compAllRefl #QNAT w) (#compAllRefl #QNAT w) eqt eqi




NUM-equalInType-QNAT : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #QNAT (#NUM k) (#NUM k)
NUM-equalInType-QNAT i w k = eqTypesQNAT , Mod.∀𝕎-□ M (λ w' e' → #weakMonEq-#NUM w' k)


equalInTypeN0 : (i : ℕ) (w : 𝕎·) → equalInType i w #NAT #N0 #N0
equalInTypeN0 i w = NUM-equalInType-NAT i w 0


equalInTypeN1 : (i : ℕ) (w : 𝕎·) → equalInType i w #NAT #N1 #N1
equalInTypeN1 i w = NUM-equalInType-NAT i w 1


eqTypesFALSE : {w : 𝕎·} {i : ℕ}
               → equalTypes i w #FALSE #FALSE
eqTypesFALSE {w} {i} rewrite #FALSE≡#EQ =
  eqTypesEQ←
    eqTypesNAT
    (equalInTypeN0 i w)
    (equalInTypeN1 i w)


eqTypesNEG← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
               → equalTypes i w A B
               → equalTypes i w (#NEG A) (#NEG B)
eqTypesNEG← {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B =
  eqTypesFUN← eqt eqTypesFALSE


eqTypesUniv : (w : 𝕎·) (n i : ℕ) (p : i < n) → equalTypes n w (#UNIV i) (#UNIV i)
eqTypesUniv w n i p = EQTUNIV i p (compAllRefl (UNIV i) w) (compAllRefl (UNIV i) w)



∀𝕎-□·-#strongMonEq-#N0 : (w : 𝕎·) → ∀𝕎 w (λ w' e → □· w' (λ w'' _ → #strongMonEq w'' #N0 #N0))
∀𝕎-□·-#strongMonEq-#N0 w w1 e1 = Mod.∀𝕎-□ M (λ w2 e2 → #strongMonEq-#N0 w2)


∀𝕎-□·-#⇛!sameℕ-#N0 : (w : 𝕎·) → ∀𝕎 w (λ w' e → □· w' (λ w'' _ → #⇛!sameℕ w'' #N0 #N0))
∀𝕎-□·-#⇛!sameℕ-#N0 w w1 e1 = Mod.∀𝕎-□ M (λ w2 e2 → #⇛!sameℕ-#N0 w2)


eqTypesTRUE : {w : 𝕎·} {i : ℕ} → equalTypes i w #TRUE #TRUE
eqTypesTRUE {w} {i} =
  EQTEQ #N0 #N0 #N0 #N0 #NAT #NAT
        (#compAllRefl #TRUE w) (#compAllRefl #TRUE w)
        (eqTypes-mon (uni i) eqTypesNAT)
        (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqTypesNAT))
        (∀𝕎-□·-#strongMonEq-#N0 w) --(∀𝕎-□·-#⇛!sameℕ-#N0 w)
        (∀𝕎-□·-#strongMonEq-#N0 w) --(∀𝕎-□·-#⇛!sameℕ-#N0 w)





eqTypesSQUASH← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w (#SQUASH A) (#SQUASH B)
eqTypesSQUASH← {w} {i} {A} {B} eqt rewrite #SQUASH≡#SET A | #SQUASH≡#SET B = eqt1
  where
    eqb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #TRUE a₁ a₂ → equalTypes i w' (sub0 a₁ ⌞ A ⌟) (sub0 a₂ ⌞ B ⌟))
    eqb w1 e1 a₁ a₂ eqa rewrite sub0⌞⌟ a₁ A | sub0⌞⌟ a₂ B = eqTypes-mon (uni i) eqt w1 e1

    eqt1 : equalTypes i w (#SET #TRUE ⌞ A ⌟) (#SET #TRUE ⌞ B ⌟)
    eqt1 = eqTypesSET← (eqTypes-mon (uni i) eqTypesTRUE) eqb


eqTypesUNION← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w C D
                  → equalTypes i w (#UNION A C) (#UNION B D)
eqTypesUNION← {w} {i} {A} {B} {C} {D} eqt1 eqt2 =
  EQTUNION A C B D (#compAllRefl (#UNION A C) w) (#compAllRefl (#UNION B D) w)
           (eqTypes-mon (uni i) eqt1) (eqTypes-mon (uni i) eqt2)
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt1))
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt2))


eqTypesQTUNION← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w C D
                  → equalTypes i w (#QTUNION A C) (#QTUNION B D)
eqTypesQTUNION← {w} {i} {A} {B} {C} {D} eqt1 eqt2 =
  EQTQTUNION A C B D (#compAllRefl (#QTUNION A C) w) (#compAllRefl (#QTUNION B D) w)
           (eqTypes-mon (uni i) eqt1) (eqTypes-mon (uni i) eqt2)
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt1))
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt2))


equalInType→equalTypes-aux : (n i : ℕ) (p : i < n) (w : 𝕎·) (a b : CTerm)
                              → equalInType n w (#UNIV i) a b
                              → equalTypes i w a b
equalInType→equalTypes-aux n i p w a b (eqt , eqi) =
  EQTBAR (eqInType-⇛-UNIV i n p w (#UNIV i) (#UNIV i) a b (compAllRefl (UNIV i) w) (compAllRefl (UNIV i) w) eqt eqi)



{--
equalTypes<s : (i : ℕ) (w : 𝕎·) (a b : CTerm)
              → equalTypes i w a b
              → equalTypes (suc i) w a b
equalTypes<s i w a b (EQTNAT x x₁) = {!!}
equalTypes<s i w a b (EQTQNAT x x₁) = {!!}
equalTypes<s i w a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
equalTypes<s i w a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
equalTypes<s i w a b (EQTFREE x x₁) = {!!}
equalTypes<s i w a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI A1 B1 A2 B2 x x₁
        (λ w' e' → equalTypes<s i w' A1 A2 (eqta w' e'))
        (λ w' e' a₁ a₂ ea → {!!})
        {!!} {!!}
equalTypes<s i w a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = {!!}
equalTypes<s i w a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = {!!}
equalTypes<s i w a b (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) = {!!}
equalTypes<s i w a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = {!!}
equalTypes<s i w a b (EQTSQUASH A1 A2 x x₁ eqtA exta) = {!!}
equalTypes<s i w a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) = {!!}
equalTypes<s i w a b (EQTUNIV i₁ p x x₁) = {!!}
equalTypes<s i w a b (EQTBAR x) = {!!}
--}



≡univ→eqTypes : {u : univs} {n : ℕ} → u ≡ uni n → {w : 𝕎·} {A B : CTerm}
                 → eqTypes (uni n) w A B
                 → eqTypes u w A B
≡univ→eqTypes {u} {n} e {w} {A} {B} eqt rewrite e = eqt



equalTypes-LIFT : (n : ℕ) (w : 𝕎·) (u v a b : CTerm)
                  → u #⇛ #LIFT a at w
                  → v #⇛ #LIFT b at w
                  → equalTypes n w a b
                  → equalTypes (suc n) w u v
equalTypes-LIFT n w u v a b c₁ c₂ eqt =
  EQTLIFT a b
          c₁ c₂
          eqta
          exta
  where
    eqta0 : ∀𝕎 w (λ w' _ → equalTypes n w' a b)
    eqta0 w' e' = eqTypes-mon (uni n) {a} {b} eqt w' e'

    eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U (uni (suc n))) w' a b)
    eqta w' e' = ≡univ→eqTypes (↓U-uni (suc n)) (eqta0 w' e')

    exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U (uni (suc n))) w (eqta w e) a b)
    exta rewrite ↓U-uni (suc n) = wPredExtIrr-eqInType eqta0



equalTypes-LIFT2 : (n : ℕ) (w : 𝕎·) (a b : CTerm)
                   → equalTypes n w a b
                   → equalTypes (suc n) w (#LIFT a) (#LIFT b)
equalTypes-LIFT2 n w a b eqt =
  equalTypes-LIFT n w (#LIFT a) (#LIFT b) a b
                  (#compAllRefl (#LIFT a) w) (#compAllRefl (#LIFT b) w)
                  eqt



uniUpTo→suc : {n m : ℕ} (q : m < n) → uniUpTo n m q ≡ uniUpTo (suc n) m (<-trans q (n<1+n n))
uniUpTo→suc {n} {m} q with m <? n
... | yes z = ≡uniUpTo n m q z
... | no z = ⊥-elim (z q)



equalTypes< : {n i : ℕ} (p : i < n) (w : 𝕎·) (a b : CTerm)
              → equalTypes i w a b
              → equalTypes n w (#↑T p a) (#↑T p b)
equalTypes< {suc n} {i} p w a b eqt = equalTypes-LIFT n w (#↑T p a) (#↑T p b) (#↑Ts p a) (#↑Ts p b) (≡→#compAllRefl w (#↑T≡#↑Ts p a)) (≡→#compAllRefl w (#↑T≡#↑Ts p b)) eqt'
  where
    eqt' : equalTypes n w (#↑Ts p a) (#↑Ts p b)
    eqt' with i <? n
    ... | yes q = equalTypes< {n} {i} q w a b eqt
    ... | no q rewrite <s→¬<→≡ p q = eqt



equalInType→equalTypes : {n i : ℕ} (p : i < n) (w : 𝕎·) (a b : CTerm)
                          → equalInType n w (#UNIV i) a b
                          → equalTypes n w (#↑T p a) (#↑T p b)
equalInType→equalTypes {n} {i} p w a b eqi = equalTypes< {n} {i} p w a b (equalInType→equalTypes-aux n i p w a b eqi)



equalInType-PI : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                 → ∀𝕎 w (λ w' _ → isType u w' A)
                 → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                 → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
                 → equalInType u w (#PI A B) f g
equalInType-PI {u} {w} {A} {B} {f} {g} ha hb eqi =
  eqTypesPI← ha hb ,
  Mod.∀𝕎-□ M aw
  where
    aw : ∀𝕎 w (λ w' e → PIeq (eqInType (uni u) w' (ha w' e))
                               (λ a1 a2 ea → eqInType (uni u) w' (hb w' e a1 a2 (TEQrefl-equalTypes u w' A A (ha w' e) , eqInType-extl1 A A (ha w' e) (TEQrefl-equalTypes u w' A A (ha w' e)) ea)))
--                               (λ a1 a2 ea → eqInType (uni u) w' (eqTypesPI←.eqtb' w' e a1 a2 ea))
                               f g)
    aw w1 e1 a₁ a₂ ea = eqInType-extl1 {u} {w1} {sub0 a₁ B}
                                       (sub0 a₁ B) (sub0 a₂ B)
                                       (fst (eqi w1 e1 a₁ a₂ (ha w1 e1 , ea)))
                                       (hb w1 e1 a₁ a₂ (TEQrefl-equalTypes u w1 A A (ha w1 e1) , eqInType-extl1 A A (ha w1 e1) (TEQrefl-equalTypes u w1 A A (ha w1 e1)) ea))
                                       (snd (eqi w1 e1 a₁ a₂ (ha w1 e1 , ea)))



equalInType-FUN : {u : ℕ} {w : 𝕎·} {A B f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → isType u w' B)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
                  → equalInType u w (#FUN A B) f g
equalInType-FUN {u} {w} {A} {B} {f} {g} ha hb i rewrite #FUN≡#PI A B =
  equalInType-PI ha hb' eqi'
  where
    hb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ B ⌟))
    hb' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ B = hb w1 e1

    eqi' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ ⌞ B ⌟) (#APPLY f a₁) (#APPLY g a₂))
    eqi' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B = i w1 e1 a₁ a₂ ea



{--→equalInTypeFALSE : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                     → □· w (λ w' e' → Lift {0ℓ} 1ℓ ⊥)
                     → equalInType u w #FALSE a b
→equalInTypeFALSE u w a b i =
  eqTypesFALSE {w} {u} ,
  Mod.∀𝕎-□ M aw
  where
    aw : ∀𝕎 w (λ w' e → EQeq #N0 #N1 (λ t1 t2 → □· w' (λ w'' _ → #strongMonEq w'' t1 t2)) w' a b)
    aw w1 e1 = {!!}
--}



equalInType-NEG : {u : ℕ} {w : 𝕎·} {A f g : CTerm}
                  → isType u w A
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
                  → equalInType u w (#NEG A) f g
equalInType-NEG {u} {w} {A} {f} {g} ha i rewrite #NEG≡#FUN A =
  equalInType-FUN (eqTypes-mon (uni u) ha) (λ w1 e1 → eqTypesFALSE) eqi
  where
    eqi : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' #FALSE (#APPLY f a₁) (#APPLY g a₂))
    eqi w1 e1 a₁ a₂ ea = ⊥-elim (i w1 e1 a₁ a₂ ea)



equalInType-local : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                    → □· w (λ w' _ → equalInType u w' T a b)
                    → equalInType u w T a b
equalInType-local {u} {w} {T} {a} {b} i =
  EQTBAR (Mod.∀𝕎-□Func M aw i) , eqi
  where
    aw : ∀𝕎 w (λ w' e' → equalInType u w' T a b → isType u w' T)
    aw w1 e1 ei = fst ei

    aw' : ∀𝕎 w (λ w' e' → (x : equalInType u w' T a b) {--→ atbar i w' e' x--} → equalTerms u w' (fst x) a b)
    aw' w1 e1 x {--at--} = equalInType→eqInType refl {fst x} x


    aw'' : ∀𝕎 w (λ w' e' → (x : equalInType u w' T a b) (y : isType u w' T)
                          → equalTerms u w' (fst x) a b
                          → equalTerms u w' y a b)
    aw'' w1 e1 x y ei = eqInType-extl1 T T (fst x) y ei

    eqi : equalTerms u w (EQTBAR (Mod.∀𝕎-□Func M aw i)) a b
    eqi = □'-change W M i (Mod.∀𝕎-□Func M aw i) aw'' (Mod.∀𝕎-□-□' M i aw')

-- Used to go through with just??? Mod.∀𝕎-□-□' M i aw'


equalInType-LIFT→ : (n : ℕ) (w : 𝕎·) (T a b : CTerm)
                     → equalInType (suc n) w (#LIFT T) a b
                     → equalInType n w T a b
{-# TERMINATING #-}
equalInType-LIFT→ n w T a b (EQTNAT x x₁ , eqi) = ⊥-elim (LIFTneqNAT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTQNAT x x₁ , eqi) = ⊥-elim (LIFTneqQNAT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LIFTneqLT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LIFTneqQLT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTFREE x x₁ , eqi) = ⊥-elim (LIFTneqFREE (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqPI (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqSUM (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqSET (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqTUNION (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (LIFTneqEQ (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (LIFTneqUNION (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (LIFTneqQTUNION (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LIFTneqTSQUASH (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LIFTneqTTRUNC (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LIFTneqTCONST (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LIFTneqSUBSING (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (LIFTneqFFDEFS (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTUNIV i p x x₁ , eqi) = ⊥-elim (LIFTneqUNIV (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTLIFT A1 A2 x x₁ eqtA exta , eqi)
  rewrite #LIFTinj {A1} {T} (sym (#compAllVal x tt))
        | #LIFTinj {A2} {T} (sym (#compAllVal x₁ tt))
        | ↓U-uni (suc n) =
  equalInType-local (Mod.∀𝕎-□Func M (λ w' e' z → eqInType→equalInType refl (eqtA w' e') z) eqi)
equalInType-LIFT→ n w T a b (EQTBAR x , eqi) =
  equalInType-local (Mod.∀𝕎-□'-□ M x aw eqi)
    where
      aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni (suc n)) w' (#LIFT T) (#LIFT T))
                          {--→ (at : atbar x w' e' z)--}
                          → equalTerms (suc n) w' z a b
                          → equalInType n w' T a b)
      aw w' e' z {--at--} j = equalInType-LIFT→ n w' T a b (z , j)



↑T# : {i n : ℕ} (p : i < n) (t : CTerm) → CTerm
↑T# {i} {suc n} p t with i <? n
... | yes q = #LIFT (↑T# q t)
... | no q = #LIFT t -- i ≡ n


↑T≡↑T# : {i n : ℕ} (p : i < n) (t : CTerm) → ↑T p ⌜ t ⌝ ≡ ⌜ ↑T# p t ⌝
↑T≡↑T# {i} {suc n} p t with i <? n
... | yes q rewrite ↑T≡↑T# q t = refl
... | no q = refl



#↑T≡↑T# : {i n : ℕ} (p : i < n) (t : CTerm) → #↑T p t ≡ ↑T# p t
#↑T≡↑T# {i} {n} p t = CTerm≡ (↑T≡↑T# p t)



equalInType-↑T#→ : {n i : ℕ} (p : i < n) (w : 𝕎·) (T a b : CTerm)
                    → equalInType n w (↑T# p T) a b
                    → equalInType i w T a b
equalInType-↑T#→ {suc n} {i} p w T a b eqi with i <? n
... | yes q = equalInType-↑T#→ q w T a b (equalInType-LIFT→ n w (↑T# q T) a b eqi)
... | no q rewrite <s→¬<→≡ p q = equalInType-LIFT→ n w T a b eqi



equalInType-#↑T→ : {n i : ℕ} (p : i < n) (w : 𝕎·) (T a b : CTerm)
                    → equalInType n w (#↑T p T) a b
                    → equalInType i w T a b
equalInType-#↑T→ {suc n} {i} p w T a b eqi rewrite #↑T≡↑T# p T = equalInType-↑T#→ p w T a b eqi



isFam : (u : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (F G : CTerm → CTerm) → Set(lsuc(L))
isFam u w A B F G =
    isType u w A
  × ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
  × ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (F a₁) (G a₂))


isFam-local : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {F G : CTerm → CTerm}
              → □· w (λ w' _ → isFam u w' A B F G)
              → isFam u w A B F G
isFam-local {u} {w} {A} {B} {F} {G} i =
  p1 , p2 , p3
  where
    aw1 : ∀𝕎 w (λ w' e' → isFam u w' A B F G → eqTypes (uni u) w' A A)
    aw1 w' e' j = fst j

    p1 : isType u w A
    p1 = eqTypes-local (Mod.∀𝕎-□Func M aw1 i)

    p2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
    p2 w' e' a₁ a₂ eqi =
      eqTypes-local (Mod.∀𝕎-□Func M aw2 (Mod.↑□ M i e'))
      where
        aw2 : ∀𝕎 w' (λ w' _ → isFam u w' A B F G → eqTypes (uni u) w' (sub0 a₁ B) (sub0 a₂ B))
        aw2 w'' e'' j = proj₁ (snd j) w'' (⊑-refl· w'') a₁ a₂ (equalInType-mon eqi w'' e'')


    p3 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (F a₁) (G a₂))
    p3 w' e' a₁ a₂ eqi =
      equalInType-local (Mod.∀𝕎-□Func M aw3 (Mod.↑□ M i e'))
      where
        aw3 : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → isFam u w''' A B F G) e' w'' e'' → equalInType u w'' (sub0 a₁ B) (F a₁) (G a₂))
        aw3 w'' e'' j = snd (snd j) w'' (⊑-refl· w'') a₁ a₂ (equalInType-mon eqi w'' e'')


equalInType-PI→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                   → equalInType u w (#PI A B) f g
                   → isFam u w A B (#APPLY f) (#APPLY g)
{-# TERMINATING #-}
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (PIneqLT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) =
  ≡CTerm→eqTypes (sym (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt))) (sym (#PIinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt))) (eqta w (⊑-refl· w)) ,
  eqtb' ,
  eqi'
  where
    eqtb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
    eqtb' w1 e1 a₁ a₂ ea =
      ≡CTerm→eqTypes
        (→≡sub0 (sym (#PIinj2 {A} {B} {A1} {B1} (#compAllVal x tt))))
        (→≡sub0 (sym (#PIinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))))
        (eqtb w1 e1 a₁ a₂ (equalInType→eqInType (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) {eqta w1 e1} ea))

    eqi' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
    eqi' w1 e1 a₁ a₂ ea = equalInType-local (Mod.∀𝕎-□Func M aw (Mod.↑□ M eqi e1))
      where
        aw : ∀𝕎 w1 (λ w' e' → ↑wPred (λ w'' e → PIeq (eqInType (uni u) w'' (eqta w'' e))
                                                       (λ a1 a2 eqa → eqInType (uni u) w'' (eqtb w'' e a1 a2 eqa))
                                                       f g) e1 w' e'
                             → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
        aw w' e' h =
          eqInType→equalInType
            (→≡sub0 (#PIinj2 {A} {B} {A1} {B1} (#compAllVal x tt)))
            (eqtb w' (⊑-trans· e1 e') a₁ a₂
                  (equalInType→eqInType (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) {eqta w' (⊑-trans· e1 e')} (equalInType-mon ea w' e')))
            (h a₁ a₂ (equalInType→eqInType (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) {eqta w' (⊑-trans· e1 e')} (equalInType-mon ea w' e')))

equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (PIneqSET (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (PIneqTUNION (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (PIneqQTUNION (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqTTRUNC (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqTCONST (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqSUBSING (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (PIneqUNIV (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTBAR x , eqi) =
  isFam-local {u} {w} {A} {B} {#APPLY f} {#APPLY g} (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni u) w' (#PI A B) (#PI A B))
                        {--→ atbar x w' e' z--}
                        → equalTerms u w' z f g
                        → isFam u w' A B (#APPLY f) (#APPLY g))
    aw w' e' z {--at--} j = equalInType-PI→ (z , j)

{-- (Mod.∀𝕎-□Func M aw x)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes (uni u) w' (#PI A B) (#PI A B)
                        → isFam u w' A B (#APPLY f) (#APPLY g))
    aw w' e' eqt = {!!}
--}

{-- j'
  where
    eqta : ∀𝕎 w (λ w' _ → equalTypes u w' A A)
    eqta w1 e1 = {!!}

    eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → equalTerms u w' (eqta w' e) a1 a2 → equalTypes u w' (sub0 a1 B) (sub0 a2 B))
    eqtb = {!!}

    j : □· w (λ w' e → PIeq (equalTerms u w' (eqta w' e)) (λ a₁ a₂ eqa → equalTerms u w' (eqtb w' e a₁ a₂ eqa)) f g)
    j = eqInType-⇛-PI (uni u) w (#PI A B) (#PI A B) A A B B f g eqta eqtb {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}

    j' : □· w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
    j' = {!!}
--}



equalInType-SQUASH-aux→ : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                           (eqt : isType n w (#SET #TRUE ⌞ A ⌟))
                           → equalTerms n w eqt a b
                           → □· w (λ w' _ → Σ CTerm (λ t → equalInType n w' A t t))
{-# TERMINATING #-}
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTNAT x x₁) eqi = ⊥-elim (SETneqNAT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTQNAT x x₁) eqi = ⊥-elim (SETneqQNAT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (SETneqLT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (SETneqQLT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTFREE x x₁) eqi = ⊥-elim (SETneqFREE (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (SETneqPI (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (SETneqSUM (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (eqInType (uni n) w' (eqta w' e')) (λ a1 a2 eqa → eqInType (uni n) w' (eqtb w' e' a1 a2 eqa)) a b
                        → Σ CTerm (λ t → equalInType n w' A t t))
    aw w' e' (t , ea , eb) =
      t , eqInType→equalInType (sym (trans (→≡sub0 (sym (#SETinj2 {#TRUE} {⌞ A ⌟} {A1} {B1} (#compAllVal x tt)))) (sub0⌞⌟ a A)))
                                (eqtb w' e' a b ea)
                                eb
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (SETneqTUNION (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) eqi = ⊥-elim (SETneqEQ (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi = ⊥-elim (SETneqUNION (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi = ⊥-elim (SETneqQTUNION (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqTSQUASH (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqTTRUNC (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqTCONST (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqSUBSING (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi = ⊥-elim (SETneqFFDEFS (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTUNIV i p x x₁) eqi = ⊥-elim (SETneqUNIV (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqLIFT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTBAR x) eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' (#SET #TRUE ⌞ A ⌟) (#SET #TRUE ⌞ A ⌟))
                       {--→ atbar x w' e' z--}
                       → equalTerms n w' z a b
                       → □· w' (↑wPred' (λ w'' e → Σ CTerm (λ t → equalInType n w'' A t t)) e'))
    aw w' e' z {--at--} j = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) i
      where
        i : □· w' (λ w'' _ → Σ CTerm (λ t → equalInType n w'' A t t))
        i = equalInType-SQUASH-aux→ z j



equalInType-SQUASH→ : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                       → equalInType n w (#SQUASH A) a b
                       → □· w (λ w' _ → inhType n w' A)
equalInType-SQUASH→ {n} {w} {A} {a} {b} (eqt , eqi) rewrite #SQUASH≡#SET A = equalInType-SQUASH-aux→ eqt eqi



equalInType-UNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#UNION A B) a b
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
{-# TERMINATING #-}
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (UNIONneqNAT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (UNIONneqQNAT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqTUNION (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) w' a b
                       → Σ CTerm (λ y → Σ CTerm (λ z
                       → (a #⇛ #INL y at w' × b #⇛ #INL z at w' × equalInType n w' A y z)
                          ⊎
                          (a #⇛ #INR y at w' × b #⇛ #INR z at w' × equalInType n w' B y z))))
    aw w' e' (y , z , inj₁ (c₁ , c₂ , u)) = y , z , inj₁ (c₁ , c₂ , eqInType→equalInType (#UNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtA w' e') u)
    aw w' e' (y , z , inj₂ (c₁ , c₂ , u)) = y , z , inj₂ (c₁ , c₂ , eqInType→equalInType (#UNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtB w' e') u)
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (UNIONneqQTUNION (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTTRUNC (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTCONST (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqSUBSING (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : equalTypes n w' (#UNION A B) (#UNION A B))
                        {--→ atbar x w' e' z--}
                        → equalTerms n w' z a b
                        → □· w' (↑wPred' (λ w'' e → Σ CTerm (λ y₁ → Σ CTerm (λ y₂
                                                     → (a #⇛ #INL y₁ at w'' × b #⇛ #INL y₂ at w'' × equalInType n w'' A y₁ y₂)
                                                        ⊎
                                                        (a #⇛ #INR y₁ at w'' × b #⇛ #INR y₂ at w'' × equalInType n w'' B y₁ y₂))))
                                             e'))
    aw w' e' z {--at--} i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) j
      where
        j : □· w' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                             → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                ⊎
                                (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
        j = equalInType-UNION→ (z , i)




equalInType-QTUNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#QTUNION A B) a b
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
{-# TERMINATING #-}
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqNAT (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqQNAT (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (QTUNIONneqLT (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (QTUNIONneqQLT (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (QTUNIONneqFREE (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqPI (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqSUM (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqSET (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqTUNION (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (QTUNIONneqEQ (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (QTUNIONneqUNION (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) w' a b
                       → Σ CTerm (λ y → Σ CTerm (λ z
                       → (a #⇓ #INL y at w' × b #⇓ #INL z at w' × equalInType n w' A y z)
                          ⊎
                          (a #⇓ #INR y at w' × b #⇓ #INR z at w' × equalInType n w' B y z))))
    aw w' e' (y , z , inj₁ (c₁ , c₂ , u)) = y , z , inj₁ (c₁ , c₂ , eqInType→equalInType (#QTUNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtA w' e') u)
    aw w' e' (y , z , inj₂ (c₁ , c₂ , u)) = y , z , inj₂ (c₁ , c₂ , eqInType→equalInType (#QTUNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtB w' e') u)
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTTRUNC (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTCONST (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqSUBSING (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (QTUNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (QTUNIONneqUNIV (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqLIFT (compAllVal x₁ tt))
equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : equalTypes n w' (#QTUNION A B) (#QTUNION A B))
                        {--→ atbar x w' e' z--}
                        → equalTerms n w' z a b
                        → □· w' (↑wPred' (λ w'' e → Σ CTerm (λ y₁ → Σ CTerm (λ y₂
                                                     → (a #⇓ #INL y₁ at w'' × b #⇓ #INL y₂ at w'' × equalInType n w'' A y₁ y₂)
                                                        ⊎
                                                        (a #⇓ #INR y₁ at w'' × b #⇓ #INR y₂ at w'' × equalInType n w'' B y₁ y₂))))
                                             e'))
    aw w' e' z {--at--} i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) j
      where
        j : □· w' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                             → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                ⊎
                                (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
        j = equalInType-QTUNION→ (z , i)



equalInType-FUN→ : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                    → equalInType u w (#FUN A B) f g
                    → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
equalInType-FUN→ {u} {w} {A} {B} {f} {g} eqi rewrite #FUN≡#PI A B = z2
  where
    z1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ ⌞ B ⌟) (#APPLY f a₁) (#APPLY g a₂))
    z1 = snd (snd (equalInType-PI→ eqi))

    z2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
    z2 w' e' a₁ a₂ ea = ≡CTerm→equalInType (sub0⌞⌟ a₁ B ) (z1 w' e' a₁ a₂ ea)


¬equalInType-FALSE : {w : 𝕎·} {i : ℕ} {a b : CTerm} → ¬ equalInType i w #FALSE a b
{-# TERMINATING #-}
¬equalInType-FALSE {w} {i} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqPI (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSET (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqTUNION (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2 , eqi)
  rewrite #FALSE/EQinj1 {a1} {a2} {A} (#compAllVal x tt)
        | #FALSE/EQinj2 {a1} {a2} {A} (#compAllVal x tt)
        | #FALSE/EQinj3 {a1} {a2} {A} (#compAllVal x tt)
        | #FALSE/EQinj1 {b1} {b2} {B} (#compAllVal x₁ tt)
        | #FALSE/EQinj2 {b1} {b2} {B} (#compAllVal x₁ tt)
        | #FALSE/EQinj3 {b1} {b2} {B} (#compAllVal x₁ tt)
  =
  lower {0ℓ} {lsuc(L)} (Mod.□-const M (Mod.∀𝕎-□Func M aw e))
  where
    e : □· w (λ w' e → EQeq #N0 #N1 (equalTerms i w' (eqtA w' e)) w' a b)
    e = eqi

    aw : ∀𝕎 w (λ w' e' → EQeq #N0 #N1 (equalTerms i w' (eqtA w' e')) w' a b → Lift (lsuc(L)) ⊥)
    aw w' e' ea = Mod.□-const M (Mod.∀𝕎-□Func M aw' z)
      where
        z : □· w' (λ w'' e → NATeq w'' #N0 #N1)
        z = eqInType-⇛-NAT (uni i) w' #NAT #NAT #N0 #N1 (#compAllRefl #NAT w') (#compAllRefl #NAT w') (eqtA w' e') ea

        aw' : ∀𝕎 w' (λ w'' e'' → NATeq w'' #N0 #N1 → Lift (lsuc(L)) ⊥)
        aw' w'' e'' s = lift (¬#strongMonEq-N0-N1 w'' s) --(¬#⇛!sameℕ-N0-N1 w'' s)
¬equalInType-FALSE {w} {i} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqQTUNION (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTTRUNC (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTCONST (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqSUBSING (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (EQneqUNIV (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqLIFT (compAllVal x₁ tt))
¬equalInType-FALSE {w} {i} {a} {b} (EQTBAR x , eqi) =
  lower {0ℓ} {lsuc(L)} (Mod.□-const M (Mod.∀𝕎-□'-□ M x aw eqi))
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni i) w' #FALSE #FALSE) {--→ atbar x w' e' z--} → equalTerms i w' z a b → Lift (lsuc(L)) ⊥)
    aw w' e' z {--at--} j = lift (¬equalInType-FALSE (z , j))



equalInType-NEG→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {f g : CTerm}
                    → equalInType u w (#NEG A) f g
                    → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
equalInType-NEG→ {u} {w} {A} {f} {g} eqi w' e' a₁ a₂ ea rewrite #NEG≡#FUN A = ¬equalInType-FALSE z
  where
    z : equalInType u w' #FALSE (#APPLY f a₁) (#APPLY g a₂)
    z = equalInType-FUN→ eqi w' e' a₁ a₂ ea



≡univ→eqInType : {u : univs} {n : ℕ} → u ≡ uni n → {w : 𝕎·} {A B a b : CTerm}
                  → (eqt₁ : eqTypes (uni n) w A B)
                  → eqInType (uni n) w eqt₁ a b
                  → (eqt₂ : eqTypes u w A B)
                  → eqInType u w eqt₂ a b
≡univ→eqInType {u} {n} e {w} {A} {B} {a} {b} eqt₁ eqi eqt₂ rewrite e =
  eqInType-extl1 B B eqt₁ eqt₂ eqi



equalInType-LIFT← : (n : ℕ) (w : 𝕎·) (T a b : CTerm)
                     → equalInType n w T a b
                     → equalInType (suc n) w (#LIFT T) a b
equalInType-LIFT← n w T a b eqi =
  equalTypes-LIFT n w (#LIFT T) (#LIFT T) T T (#compAllRefl (#LIFT T) w) (#compAllRefl (#LIFT T) w) (fst eqi) ,
  j
  where
    eqta0 : ∀𝕎 w (λ w' _ → equalTypes n w' T T)
    eqta0 w' e' = eqTypes-mon (uni n) {T} {T} (fst eqi) w' e'

    eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U (uni (suc n))) w' T T)
    eqta w' e' = ≡univ→eqTypes (↓U-uni (suc n)) (eqta0 w' e')

    j : □· w (λ w' e → eqInType (↓U (uni (suc n))) w' (eqta w' e) a b)
    j = Mod.∀𝕎-□ M aw
      where
        aw : ∀𝕎 w (λ w' e → eqInType (↓U (uni (suc n))) w' (eqta w' e) a b)
        aw w' e' = ≡univ→eqInType (↓U-uni (suc n)) (eqta0 w' e') (equalInType→eqInType refl {eqta0 w' e'} (equalInType-mon eqi w' e')) (eqta w' e')



equalInType-↑T#← : {n i : ℕ} (p : i < n) (w : 𝕎·) (T a b : CTerm)
                    → equalInType i w T a b
                    → equalInType n w (↑T# p T) a b
equalInType-↑T#← {suc n} {i} p w T a b eqi with i <? n
... | yes q = equalInType-LIFT← n w (↑T# q T) a b (equalInType-↑T#← q w T a b eqi)
... | no q rewrite <s→¬<→≡ p q = equalInType-LIFT← n w T a b eqi



equalInType-#↑T← : {n i : ℕ} (p : i < n) (w : 𝕎·) (T a b : CTerm)
                    → equalInType i w T a b
                    → equalInType n w (#↑T p T) a b
equalInType-#↑T← {suc n} {i} p w T a b eqi rewrite #↑T≡↑T# p T = equalInType-↑T#← p w T a b eqi



equalInType-NEG-↑T→ : {n i : ℕ} (p : i < n) {w : 𝕎·} {A : CTerm} {f g : CTerm}
                       → equalInType n w (#NEG (#↑T p A)) f g
                       → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' A a₁ a₂)
equalInType-NEG-↑T→ {n} {i} p {w} {A} {f} {g} eqi w' e' a₁ a₂ ea =
  z (equalInType-#↑T← p w' A a₁ a₂ ea)
  where
    z : ¬ equalInType n w' (#↑T p A) a₁ a₂
    z = equalInType-NEG→ eqi w' e' a₁ a₂



equalTypes→equalInType-UNIV : {n i : ℕ} (p : i < n) {w : 𝕎·} {a b : CTerm}
                              → equalTypes i w a b
                              → equalInType n w (#UNIV i) a b
equalTypes→equalInType-UNIV {n} {i} p {w} {a} {b} eqt =
  eqTypesUniv w n i p , □·EqTypes→uniUpTo {i} {n} {p} (Mod.∀𝕎-□ M (eqTypes-mon (uni i) eqt))



equalInType-SUM : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                  → □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
                  → equalInType u w (#SUM A B) f g
equalInType-SUM {u} {w} {A} {B} {f} {g} ha hb eqi =
  eqTypesSUM← ha hb ,
  Mod.∀𝕎-□Func M
    (λ w' e' (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) →
      a₁ , a₂ , b₁ , b₂ ,
      equalInType→eqInType {u} {w'} {A} {A} {A} refl {ha w' e'} ea ,
      c₁ , c₂ ,
      equalInType→eqInType
        {u} {w'} {sub0 a₁ B} {sub0 a₁ B} {sub0 a₂ B} refl
        {equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w' e' a₁ a₂ (equalInType→eqInType {u} {w'} {A} {A} {A} refl {ha w' e'} ea)}
        eb)
    eqi





□·-wPred'-#weakMonEq : (w w' : 𝕎·) (e' : w ⊑· w') (a₁ a₂ : CTerm)
                                   → □· w' (λ w'' _ → #weakMonEq w'' a₁ a₂)
                                   → □· w' (↑wPred' (λ w'' e → #weakMonEq w'' a₁ a₂) e')
□·-wPred'-#weakMonEq w w' e' a₁ a₂ i = Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w' (λ w'' e'' → #weakMonEq w'' a₁ a₂ → ↑wPred' (λ w''' e → #weakMonEq w''' a₁ a₂) e' w'' e'')
    aw w1 e1 z j = z



□·-wPred'-#strongMonEq : (w w' : 𝕎·) (e' : w ⊑· w') (a₁ a₂ : CTerm)
                            → □· w' (λ w'' _ → #strongMonEq w'' a₁ a₂)
                            → □· w' (↑wPred' (λ w'' e → #strongMonEq w'' a₁ a₂) e')
□·-wPred'-#strongMonEq w w' e' a₁ a₂ i = Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w' (λ w'' e'' → #strongMonEq w'' a₁ a₂ → ↑wPred' (λ w''' e → #strongMonEq w''' a₁ a₂) e' w'' e'')
    aw w1 e1 z j = z



equalInType-EQ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                  → isType u w A
                  → □· w (λ w' _ → EQeq a b (equalInType u w' A) w' f g)
                  → equalInType u w (#EQ a b A) f g
equalInType-EQ {u} {w} {a} {b} {A} {f} {g} ha eqi =
  eqTypesEQ← ha ma mb , j
  where
    ma : equalInType u w A a a
    ma = equalInType-local (Mod.∀𝕎-□Func M aw eqi)
      where
        aw : ∀𝕎 w (λ w' e' → EQeq a b (equalInType u w' A) w' f g → equalInType u w' A a a)
        aw w' e h = equalInType-refl h

    mb : equalInType u w A b b
    mb = equalInType-local (Mod.∀𝕎-□Func M aw eqi)
      where
        aw : ∀𝕎 w (λ w' e' → EQeq a b (equalInType u w' A) w' f g → equalInType u w' A b b)
        aw w' e h = equalInType-refl (equalInType-sym h)

    j : equalTerms u w (eqTypesEQ← ha ma mb) f g
    j = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → EQeq a b (equalInType u w' A) w' f g
                            → EQeq a b (eqInType (uni u) w' (eqTypes-mon (uni u) ha w' e')) w' f g)
        aw w' e h = equalInType→eqInType {u} {w'} {A} {A} {A} refl {eqTypes-mon (uni u) ha w' e} h




equalInType-SUM→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                    → equalInType u w (#SUM A B) f g
                    → □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
{-# TERMINATING #-}
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms u w' (eqta w' e')) (λ a1 a2 eqa → equalTerms u w' (eqtb w' e' a1 a2 eqa)) w' f g
                       → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
    aw w' e' (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea' , c₁ , c₂ , eb'
      where
        ea' : equalInType u w' A a₁ a₂
        ea' = eqInType→equalInType {u} {w'} {A} {A1} {A2} (#SUMinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqta w' e') ea

        eb' : equalInType u w' (sub0 a₁ B) b₁ b₂
        eb' = eqInType→equalInType {u} {w'} {sub0 a₁ B} {sub0 a₁ B1} {sub0 a₂ B2} (→≡sub0 (#SUMinj2 {A} {B} {A1} {B1} (#compAllVal x tt))) (eqtb w' e' a₁ a₂ ea) eb

equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqTCONST (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (SUMneqUNIV (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
equalInType-SUM→ {u} {w} {A} {B} {f} {g} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' (#SUM A B) (#SUM A B))
                       → equalTerms u w' z f g
                       → □· w' (↑wPred' (λ w'' e → SUMeq (equalInType u w'' A) (λ a b ea → equalInType u w'' (sub0 a B)) w'' f g) e'))
    aw w' e' z ei = Mod.∀𝕎-□Func M (λ w1 e1 h z → h) (equalInType-SUM→ (z , ei))



equalInType-SUM→₂ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                     → equalInType u w (#SUM A B) f g
                     → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
{-# TERMINATING #-}
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) w1 e1 a₁ a₂ ea =
  ≡CTerm→eqTypes
    (→≡sub0 (sym (#SUMinj2 {A} {B} {A1} {B1} (#compAllVal x tt))))
    (→≡sub0 (sym (#SUMinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))))
    (eqtb w1 e1 a₁ a₂ (equalInType→eqInType (#SUMinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) {eqta w1 e1} ea))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqTCONST (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (SUMneqUNIV (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (EQTBAR x , eqi) w1 e1 a₁ a₂ ea =
  eqTypes-local (Mod.∀𝕎-□'-□ M (Mod.↑□ M x e1) aw (Mod.↑□' M {w} {_} {λ w' e' z → equalTerms u w' z f g} x e1 eqi))
  where
    aw : ∀𝕎 w1 (λ w' e' → (z : ↑wPred (λ w'' e → equalTypes u w'' (#SUM A B) (#SUM A B)) e1 w' e')
                         → equalTerms u w' z f g → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
    aw w' e' z eqj = equalInType-SUM→₂ (z , eqj) w' (⊑-refl· _) a₁ a₂ (equalInType-mon ea w' e')



equalInType-EQ→ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                  → equalInType u w (#EQ a b A) f g
                  → □· w (λ w' _ → EQeq a b (equalInType u w' A) w' f g)
{-# TERMINATING #-}
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqPI (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSET (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqTUNION (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi)
  rewrite sym (#EQinj1 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
        | sym (#EQinj2 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
        | sym (#EQinj3 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a b (equalTerms u w' (eqtA w' e')) w' f g
                        → EQeq a b (equalInType u w' A) w' f g)
    aw w' e' ea = ea'
      where
        ea' : equalInType u w' A a b
        ea' = eqInType→equalInType {u} {w'} {A} {A} {B} refl (eqtA w' e') ea

equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqQTUNION (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTTRUNC (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTCONST (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqSUBSING (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (EQneqUNIV (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqLIFT (compAllVal x₁ tt))
equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} (EQTBAR x , eqi) =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' (#EQ a b A) (#EQ a b A))
                       → equalTerms u w' z f g
                       → □· w' (↑wPred' (λ w'' e → EQeq a b (equalInType u w'' A) w'' f g) e'))
    aw w' e' z ei = Mod.∀𝕎-□Func M (λ w1 e1 h z → h) (equalInType-EQ→ (z , ei))



equalInType-EQ-QNAT→ : {u : ℕ} {w : 𝕎·} {a b : CTerm} {f g : CTerm}
                        → equalInType u w (#EQ a b #QNAT) f g
                        → □· w (λ w' _ → #weakMonEq w' a b)
equalInType-EQ-QNAT→ {u} {w} {a} {b} {f} {g} eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-EQ→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a b (equalInType u w' #QNAT) w' f g → □· w' (↑wPred' (λ w'' e → #weakMonEq w'' a b) e'))
    aw w' e ea = Mod.∀𝕎-□Func M (λ w1 e1 z _ → z) (equalInType-QNAT→ u w' a b ea)



#weakMonEq→TSQUASHeq-#NAT : {i : ℕ} {w : 𝕎·} {a b : CTerm}
                             → #weakMonEq! w a b
                             → TSQUASHeq (equalInType i w #NAT) w a b
#weakMonEq→TSQUASHeq-#NAT {i} {w} {a} {b} h =
  TSQUASH-eq→ (TSQUASH-eq-base (#NUM n) (#NUM n) tt tt c₁ c₂ (NUM-equalInType-NAT i w n))
  where
    n : ℕ
    n = fst (lower (h w (⊑-refl· _)))

    c₁ : ∼C! w a (#NUM n)
    c₁ = #⇓!→∼C! {w} {a} {#NUM n} (fst (snd (lower (h w (⊑-refl· _)))))

    c₂ : ∼C! w b (#NUM n)
    c₂ = #⇓!→∼C! {w} {b} {#NUM n} (snd (snd (lower (h w (⊑-refl· _)))))


→equalInType-QTNAT : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → □· w (λ w' _ → #weakMonEq! w' a b)
                      → equalInType i w #QTNAT a b
→equalInType-QTNAT i w a b j =
  ≡CTerm→equalInType (sym #QTNAT≡) (equalInTypeTSQUASH← (Mod.∀𝕎-□Func M aw j))
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq! w' a b → TSQUASHeq (equalInType i w' #NAT) w' a b)
    aw w' e h = #weakMonEq→TSQUASHeq-#NAT h


NUM-equalInType-QTNAT : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #QTNAT (#NUM k) (#NUM k)
NUM-equalInType-QTNAT i w k =
  →equalInType-QTNAT i w (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w' e' → #weakMonEq!-#NUM w' k))



#weakMonEq→TSQUASHeq-#NAT! : {i : ℕ} {w : 𝕎·} {a b : CTerm}
                             → #weakMonEq! w a b
                             → TSQUASHeq (equalInType i w #NAT!) w a b
#weakMonEq→TSQUASHeq-#NAT! {i} {w} {a} {b} h =
  TSQUASH-eq→ (TSQUASH-eq-base (#NUM n) (#NUM n) tt tt c₁ c₂ (NUM-equalInType-NAT! i w n))
  where
    n : ℕ
    n = fst (lower (h w (⊑-refl· _)))

    c₁ : ∼C! w a (#NUM n)
    c₁ = #⇓!→∼C! {w} {a} {#NUM n} (fst (snd (lower (h w (⊑-refl· _)))))

    c₂ : ∼C! w b (#NUM n)
    c₂ = #⇓!→∼C! {w} {b} {#NUM n} (snd (snd (lower (h w (⊑-refl· _)))))


→equalInType-QTNAT! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → □· w (λ w' _ → #weakMonEq! w' a b)
                      → equalInType i w #QTNAT! a b
→equalInType-QTNAT! i w a b j =
  ≡CTerm→equalInType (sym #QTNAT!≡) (equalInTypeTSQUASH← (Mod.∀𝕎-□Func M aw j))
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq! w' a b → TSQUASHeq (equalInType i w' #NAT!) w' a b)
    aw w' e h = #weakMonEq→TSQUASHeq-#NAT! h


NUM-equalInType-QTNAT! : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #QTNAT! (#NUM k) (#NUM k)
NUM-equalInType-QTNAT! i w k =
  →equalInType-QTNAT! i w (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w' e' → #weakMonEq!-#NUM w' k))

\end{code}[hide]
