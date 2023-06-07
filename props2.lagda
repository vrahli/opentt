\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

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
open import newChoice
open import mod
open import encode


--module props2 (bar : Bar) where
module props2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_tnat(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_ttrunc(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_tconst(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_subsing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_isect(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_noseq(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_term(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

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



eqTypesW← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#WT A B) (#WT C D)
eqTypesW← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTW A B C D (#compAllRefl (#WT A B) w) (#compAllRefl (#WT C D) w)
        eqta
        (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb)
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {C} {D} eqta eqtb))



eqTypesM← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#MT A B) (#MT C D)
eqTypesM← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTM A B C D (#compAllRefl (#MT A B) w) (#compAllRefl (#MT C D) w)
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


→≡equalTypes : {i : ℕ} {w : 𝕎·} {a1 a2 b1 b2 : CTerm}
                → a1 ≡ a2
                → b1 ≡ b2
                → equalTypes i w a1 b1
                → equalTypes i w a2 b2
→≡equalTypes {i} {w} {a1} {a2} {b1} {b2} e1 e2 h rewrite e1 | e2 = h


→≡equalInType : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                → T ≡ U
                → equalInType i w T a b
                → equalInType i w U a b
→≡equalInType {i} {w} {T} {U} {a} {b} e h rewrite e = h


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



eqTypes-local : {u : univs} {w : 𝕎·} {A B : CTerm}
                → □· w (λ w' _ → eqTypes u w' A B)
                → eqTypes u w A B
eqTypes-local {u} {w} {A} {B} i =
  EQTBAR i


abstract
  equalInType-PURE→ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                         → equalInType n w #PURE a b
                         → □· w (λ w' _ → PUREeq a b)
  equalInType-PURE→ {n} {w} {a} {b} (eqt , eqi) = concl #PURE #PURE eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #PURE → T2' ≡ #PURE → □· w' (λ w'' _ → PUREeq a' b'))
            → T1 ≡ #PURE → T2 ≡ #PURE → □· w (λ w' _ → PUREeq a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → PUREeq a b → PUREeq a b)
          aw w' e' p = p
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PUREneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → PUREeq a b) e'))
          aw w' e' z at i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) (ind {u} {w'} {T1} {T2} z {a} {b} i (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes n w T1 T2) (eqi : equalTerms n w eqt a b)
              → T1 ≡ #PURE → T2 ≡ #PURE → □· w (λ w' _ → PUREeq a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #PURE → T2 ≡ #PURE → □· w (λ w' _ → PUREeq a b))
          ind eqt a b eqi


abstract
  equalInType-NOSEQ→ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                         → equalInType n w #NOSEQ a b
                         → □· w (λ w' _ → NOSEQeq a b)
  equalInType-NOSEQ→ {n} {w} {a} {b} (eqt , eqi) = concl #NOSEQ #NOSEQ eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #NOSEQ → T2' ≡ #NOSEQ → □· w' (λ w'' _ → NOSEQeq a' b'))
            → T1 ≡ #NOSEQ → T2 ≡ #NOSEQ → □· w (λ w' _ → NOSEQeq a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → NOSEQeq a b → NOSEQeq a b)
          aw w' e' p = p
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (NOSEQneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → NOSEQeq a b) e'))
          aw w' e' z at i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) (ind {u} {w'} {T1} {T2} z {a} {b} i (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes n w T1 T2) (eqi : equalTerms n w eqt a b)
              → T1 ≡ #NOSEQ → T2 ≡ #NOSEQ → □· w (λ w' _ → NOSEQeq a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #NOSEQ → T2 ≡ #NOSEQ → □· w (λ w' _ → NOSEQeq a b))
          ind eqt a b eqi


→≡TERMeq : {w : 𝕎·} (t1 t2 u1 u2 : CTerm)
            → t1 ≡ u1
            → t2 ≡ u2
            → TERMeq w t1 t2
            → TERMeq w u1 u2
→≡TERMeq {w} t1 t2 u1 u2 eqt equ teq rewrite eqt | equ = teq


abstract
  equalInType-TERM→ : {n : ℕ} {w : 𝕎·} {t a b : CTerm}
                         → equalInType n w (#TERM t) a b
                         → □· w (λ w' _ → TERMeq w' t t)
  equalInType-TERM→ {n} {w} {t} {a} {b} (eqt , eqi) = concl (#TERM t) (#TERM t) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #TERM t → T2' ≡ #TERM t → □· w' (λ w'' _ → TERMeq w'' t t))
            → T1 ≡ #TERM t → T2 ≡ #TERM t → □· w (λ w' _ → TERMeq w' t t)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 eq2
        rewrite eq1 | eq2
        = Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → TERMeq w' t1 t2 → TERMeq w' t t)
          aw w' e' p = →≡TERMeq {w'} t1 t2 t t (#TERMinj {t1} {t} (sym (#compAllVal x tt))) (#TERMinj {t2} {t} (sym (#compAllVal x₁ tt))) p
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (TERMneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → TERMeq w'' t t) e'))
          aw w' e' z at i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) (ind {u} {w'} {T1} {T2} z {a} {b} i (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes n w T1 T2) (eqi : equalTerms n w eqt a b)
              → T1 ≡ #TERM t → T2 ≡ #TERM t → □· w (λ w' _ → TERMeq w' t t)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #TERM t → T2 ≡ #TERM t → □· w (λ w' _ → TERMeq w' t t))
          ind eqt a b eqi


abstract
  equalInType-SUM→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                     → equalInType u w (#SUM A B) f g
                     → □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
  equalInType-SUM→ {u} {w} {A} {B} {f} {g} (eqt , eqi) = concl (#SUM A B) (#SUM A B) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {f g : CTerm} (eqi : equalTerms u w eqt f g)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {f' g' : CTerm} (eqi' : equalTerms u' w' eqt' f' g')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #SUM A B → T2' ≡ #SUM A B
                → □· w' (λ w' _ → SUMeq (equalInType u' w' A) (λ a b ea → equalInType u' w' (sub0 a B)) w' f' g'))
            → T1 ≡ #SUM A B → T2 ≡ #SUM A B
            → □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 =
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
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {f} {g} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z f g
                              → □· w' (↑wPred' (λ w'' e → SUMeq (equalInType u w'' A) (λ a b ea → equalInType u w'' (sub0 a B)) w'' f g) e'))
          aw w' e' z at j = Mod.∀𝕎-□Func M (λ w1 e1 h z → h) (ind {u} {w'} {T1} {T2} z {f} {g} j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes u w T1 T2) (eqi : equalTerms u w eqt f g)
              → T1 ≡ #SUM A B → T2 ≡ #SUM A B
              → □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {u} {w} {T1} {T2} eqt {f} {g} eqi
            → T1 ≡ #SUM A B → T2 ≡ #SUM A B
            → □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g))
          ind eqt f g eqi


codom-fam-local : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0}
                  → □· w (λ w' _ → ∀𝕎 w' (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B)))
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
codom-fam-local {u} {w} {A} {B} i w' e' a₁ a₂ eqi =
  eqTypes-local (Mod.∀𝕎-□Func M aw2 (Mod.↑□ M i e'))
  where
    aw2 : ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                         → eqTypes (uni u) w' (sub0 a₁ B) (sub0 a₂ B))
    aw2 w'' e'' j = j w'' (⊑-refl· w'') a₁ a₂ (equalInType-mon eqi w'' e'')


abstract
  equalInType-SUM→₂ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                      → equalInType u w (#SUM A B) f g
                      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
  equalInType-SUM→₂ {u} {w} {A} {B} {f} {g} (eqt , eqi) = concl (#SUM A B) (#SUM A B) eqt refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #SUM A B → T2' ≡ #SUM A B
                → ∀𝕎 w' (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u' w' A a₁ a₂) → equalTypes u' w' (sub0 a₁ B) (sub0 a₂ B)))
            → T1 ≡ #SUM A B → T2 ≡ #SUM A B
            → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 w1 e1 a₁ a₂ ea rewrite eq1 | eq2 =
        ≡CTerm→eqTypes
          (→≡sub0 (sym (#SUMinj2 {A} {B} {A1} {B1} (#compAllVal x tt))))
          (→≡sub0 (sym (#SUMinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))))
          (eqtb w1 e1 a₁ a₂ (equalInType→eqInType (#SUMinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) {eqta w1 e1} ea))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 =
        codom-fam-local {u} {w} {A} {B} (∀𝕎-□at W M x aw)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z
                              → ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → equalInType u w'' A a₁ a₂ → equalTypes u w'' (sub0 a₁ B) (sub0 a₂ B)))
          aw w' e' z at = ind {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes u w T1 T2)
              → T1 ≡ #SUM A B → T2 ≡ #SUM A B
              → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {u} {w} {T1} {T2} eqt
            → T1 ≡ #SUM A B → T2 ≡ #SUM A B
            → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B)))
          ind eqt


abstract
  equalInType-SUM→₀ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                      → equalInType u w (#SUM A B) f g
                      → isType u w A
  equalInType-SUM→₀ {u} {w} {A} {B} {f} {g} (eqt , eqi) = concl (#SUM A B) (#SUM A B) eqt refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #SUM A B → T2' ≡ #SUM A B
                → isType u' w' A)
            → T1 ≡ #SUM A B → T2 ≡ #SUM A B
            → isType u w A
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 =
        ≡CTerm→eqTypes
          (sym (#SUMinj1 {A} {B} {A1} {B1} (#compAllVal x tt)))
          (sym (#SUMinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt)))
          (eqta w (⊑-refl· w))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 =
        eqTypes-local (∀𝕎-□at W M x aw)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z → isType u w' A)
          aw w' e' z at = ind {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes u w T1 T2)
              → T1 ≡ #SUM A B → T2 ≡ #SUM A B
              → isType u w A
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {u} {w} {T1} {T2} eqt → T1 ≡ #SUM A B → T2 ≡ #SUM A B → isType u w A)
          ind eqt


abstract
  equalInType-SUM→₁ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                      → equalInType u w (#SUM A B) f g
                      → ∀𝕎 w (λ w' _ → isType u w' A)
  equalInType-SUM→₁ {u} {w} {A} {B} {f} {g} eqi w1 e1 =
    equalInType-SUM→₀ {u} {w1} {A} {B} {f} {g} (equalInType-mon eqi w1 e1)


abstract
  eqTypesFUN→₀ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
                 → equalTypes i w (#FUN A B) (#FUN C D)
                 → equalTypes i w A C
  eqTypesFUN→₀ {w} {i} {A} {B} {C} {D} eqt = concl (#FUN A B) (#FUN C D) eqt refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → T1' ≡ #FUN A B → T2' ≡ #FUN C D → equalTypes u' w' A C)
            → T1 ≡ #FUN A B → T2 ≡ #FUN C D → equalTypes u w A C
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 =
        →≡equalTypes
          (#FUN/PIinj1 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#FUN A B) T1 (sym eq1) tt))))
          (#FUN/PIinj1 {C} {D} {A2} {B2} (trans (sym eq2) (#compAllVal x₁ (≡→#isValue (#FUN C D) T2 (sym eq2) tt))))
          (eqta w (⊑-refl· w))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV m p c₁ c₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqUNIV (compAllVal c₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 =
        EQTBAR (∀𝕎-□at W M x aw)
  -- (a) This does not work
  -- EQTBAR (∀𝕎-inOpenBarFunc aw (↑inOpenBar x e'))
  -- (b) Unfolding and reducing works though:
  -- EQTBAR (λ w1 e1 → fst (x w1 (⊑-trans· e' e1)) ,
  --                     fst (snd (x w1 (⊑-trans· e' e1))) ,
  --                     λ w3 e3 z → aw w3 z (snd (snd (x w1 (⊑-trans· e' e1))) w3 e3 (⊑-trans· e' z)))
        where
          aw : ∀𝕎 w (λ w1 e1 → (z : eqTypes (uni u) w1 T1 T2) (at : at□· x w1 e1 z) → equalTypes u w1 A C)
          aw w1 e1 z at = ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2)
              → T1 ≡ #FUN A B → T2 ≡ #FUN C D → equalTypes i w A C
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {i} {w} {T1} {T2} eqt → T1 ≡ #FUN A B → T2 ≡ #FUN C D → equalTypes i w A C)
          ind eqt


abstract
  eqTypesFUN→₁ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
                 → equalTypes i w (#FUN A B) (#FUN C D)
                 → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
  eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} eqt w1 e1 =
    eqTypesFUN→₀ {w1} {i} {A} {B} {C} {D} (eqTypes-mon (uni i) eqt w1 e1)


eqTypesNEG→ : {w : 𝕎·} {i : ℕ} {A B : CTerm}
               → equalTypes i w (#NEG A) (#NEG B)
               → equalTypes i w A B
eqTypesNEG→ {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B = eqTypesFUN→₁ eqt w (⊑-refl· w)


eqTypesNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #NAT #NAT
eqTypesNAT {w} {i} = EQTNAT (#compAllRefl #NAT w) (#compAllRefl #NAT w)


eqTypesQNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #QNAT #QNAT
eqTypesQNAT {w} {i} = EQTQNAT (#compAllRefl #QNAT w) (#compAllRefl #QNAT w)


eqTypesTNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #TNAT #TNAT
eqTypesTNAT {w} {i} = EQTTNAT (#compAllRefl #TNAT w) (#compAllRefl #TNAT w)



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



eqTypesPURE← : {w : 𝕎·} {i : ℕ}
              → equalTypes i w #PURE #PURE
eqTypesPURE← {w} {i} =
  EQTPURE (#compAllRefl #PURE w) (#compAllRefl #PURE w)



eqTypesNOSEQ← : {w : 𝕎·} {i : ℕ}
              → equalTypes i w #NOSEQ #NOSEQ
eqTypesNOSEQ← {w} {i} =
  EQTNOSEQ (#compAllRefl #NOSEQ w) (#compAllRefl #NOSEQ w)


equalInType-NAT→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → equalInType i w #NAT a b
                    → □· w (λ w' _ → NATeq w' a b)
equalInType-NAT→ i w a b (eqt , eqi) =
  eqInType-⇛-NAT (uni i) w #NAT #NAT a b (#compAllRefl #NAT w) (#compAllRefl #NAT w) eqt eqi


eqTypesTERM← : {w : 𝕎·} {i : ℕ} {a b : CTerm}
                → equalInType i w #NAT a b
                → equalTypes i w (#TERM a) (#TERM b)
eqTypesTERM← {w} {i} {a} {b} a∈ =
  EQTTERM a b (#compAllRefl (#TERM a) w) (#compAllRefl (#TERM b) w) (equalInType-NAT→ i w a b a∈)


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



NUM-equalInType-NAT : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #NAT (#NUM k) (#NUM k)
NUM-equalInType-NAT i w k = eqTypesNAT , Mod.∀𝕎-□ M (λ w' e' → #strongMonEq-#NUM w' k)


isTypeNAT! : {w : 𝕎·} {i : ℕ} → isType i w #NAT!
isTypeNAT! {w} {i} = eqTypesTCONST← eqTypesNAT


NUM-equalInType-NAT! : (i : ℕ) (w : 𝕎·) (k : ℕ) → equalInType i w #NAT! (#NUM k) (#NUM k)
NUM-equalInType-NAT! i w k =
  isTypeNAT! ,
  Mod.∀𝕎-□ M (λ w' e' → Mod.∀𝕎-□ M (λ w'' e'' → #strongMonEq-#NUM w'' k) , #⇓→#⇓!-NUM w' k , #⇓→#⇓!-NUM w' k)


abstract
  equalInTypeTSQUASH→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                        → equalInType i w (#TSQUASH A) a b
                        → □· w (λ w' _ → TSQUASHeq (equalInType i w' A) w' a b)
  equalInTypeTSQUASH→ {w} {i} {a} {b} {A} (eqt , eqi) = concl (#TSQUASH A) (#TSQUASH A) eqt eqi refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #TSQUASH A → □· w' (λ w'' _ → TSQUASHeq (equalInType u' w'' A) w'' a' b'))
            → T1 ≡ #TSQUASH A → □· w (λ w' _ → TSQUASHeq (equalInType u w' A) w' a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqQNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 =
          Mod.∀𝕎-□Func M aw eqi
            where
              aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms u w' (eqtA w' e')) w' a b → TSQUASHeq (equalInType u w' A) w' a b)
              aw w1 e1 p = TSQUASHeq-ext-eq (λ a1 a2 ea → eqInType→equalInType (#TSQUASHinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqTCONST (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TSQUASHneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → TSQUASHeq (equalInType u w'' A) w'' a b) e'))
          aw w1 e1 z at h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (ind {u} {w1} {T1} {T2} z h (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt a b)
              → T1 ≡ #TSQUASH A → □· w (λ w' _ → TSQUASHeq (equalInType i w' A) w' a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #TSQUASH A → □· w (λ w' _ → TSQUASHeq (equalInType i w' A) w' a b))
          ind eqt a b eqi


abstract
  equalInTypeTTRUNC→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                        → equalInType i w (#TTRUNC A) a b
                        → □· w (λ w' _ → TTRUNCeq (equalInType i w' A) w' a b)
  equalInTypeTTRUNC→ {w} {i} {a} {b} {A} (eqt , eqi) = concl (#TTRUNC A) (#TTRUNC A) eqt eqi refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #TTRUNC A → □· w' (λ w'' _ → TTRUNCeq (equalInType u' w'' A) w'' a' b'))
            → T1 ≡ #TTRUNC A → □· w (λ w' _ → TTRUNCeq (equalInType u w' A) w' a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqQNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqTSQUASH (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 =
          Mod.∀𝕎-□Func M aw eqi
            where
              aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalTerms u w' (eqtA w' e')) w' a b → TTRUNCeq (equalInType u w' A) w' a b)
              aw w1 e1 p = TTRUNCeq-ext-eq (λ a1 a2 ea → eqInType→equalInType (#TTRUNCinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqTCONST (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TTRUNCneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → TTRUNCeq (equalInType u w'' A) w'' a b) e'))
          aw w1 e1 z at h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (ind {u} {w1} {T1} {T2} z h (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt a b)
              → T1 ≡ #TTRUNC A → □· w (λ w' _ → TTRUNCeq (equalInType i w' A) w' a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #TTRUNC A → □· w (λ w' _ → TTRUNCeq (equalInType i w' A) w' a b))
          ind eqt a b eqi



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


abstract
  equalInTypeTCONST→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                        → equalInType i w (#TCONST A) a b
                        → □· w (λ w' _ → TCONSTeq (equalInType i w' A) w' a b)
  equalInTypeTCONST→ {w} {i} {a} {b} {A} (eqt , eqi) = concl (#TCONST A) (#TCONST A) eqt eqi refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #TCONST A → □· w' (λ w'' _ → TCONSTeq (equalInType u' w'' A) w'' a' b'))
            → T1 ≡ #TCONST A → □· w (λ w' _ → TCONSTeq (equalInType u w' A) w' a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqQNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqTSQUASH (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 =
          Mod.∀𝕎-□Func M aw eqi
            where
              aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms u w' (eqtA w' e')) w' a b → TCONSTeq (equalInType u w' A) w' a b)
              aw w1 e1 p = TCONSTeq-ext-eq (λ a1 a2 ea → eqInType→equalInType {_} {_} {_} {_} {_} {a1} {a2} (#TCONSTinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (TCONSTneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → TCONSTeq (equalInType u w'' A) w'' a b) e'))
          aw w1 e1 z at h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (ind {u} {w1} {T1} {T2} z h (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt a b)
              → T1 ≡ #TCONST A → □· w (λ w' _ → TCONSTeq (equalInType i w' A) w' a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #TCONST A → □· w (λ w' _ → TCONSTeq (equalInType i w' A) w' a b))
          ind eqt a b eqi


abstract
  equalInTypeSUBSING→ : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                        → equalInType i w (#SUBSING A) a b
                        → □· w (λ w' _ → SUBSINGeq (equalInType i w' A) a b)
  equalInTypeSUBSING→ {w} {i} {a} {b} {A} (eqt , eqi) = concl (#SUBSING A) (#SUBSING A) eqt eqi refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #SUBSING A → □· w' (λ w'' _ → SUBSINGeq (equalInType u' w'' A) a' b'))
            → T1 ≡ #SUBSING A → □· w (λ w' _ → SUBSINGeq (equalInType u w' A) a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqQNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqTSQUASH (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqTCONST (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 =
          Mod.∀𝕎-□Func M aw eqi
            where
              aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalTerms u w' (eqtA w' e')) a b → SUBSINGeq (equalInType u w' A) a b)
              aw w1 e1 p = SUBSINGeq-ext-eq (λ a1 a2 ea → eqInType→equalInType {_} {_} {_} {_} {_} {a1} {a2} (#SUBSINGinj {A} {A1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (SUBSINGneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → SUBSINGeq (equalInType u w'' A) a b) e'))
          aw w1 e1 z at h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (ind {u} {w1} {T1} {T2} z h (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt a b)
              → T1 ≡ #SUBSING A → □· w (λ w' _ → SUBSINGeq (equalInType i w' A) a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #SUBSING A → □· w (λ w' _ → SUBSINGeq (equalInType i w' A) a b))
          ind eqt a b eqi


FFDEFSeq-ext-eq₀ : {w : 𝕎·} {eqa1 eqa2 : per} {x₁ x₂ t1 t2 : CTerm}
                   → x₁ ≡ x₂
                   → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                   → FFDEFSeq x₁ eqa1 w t1 t2
                   → FFDEFSeq x₂ eqa2 w t1 t2
FFDEFSeq-ext-eq₀ {w} {eqa1} {eqa2} {x₁} {x₂} {t1} {t2} eqx ext (y , h , q) rewrite eqx = y , ext x₂ y h , q


abstract
  equalInTypeFFDEFS→ : {w : 𝕎·} {i : ℕ} {a b A y : CTerm}
                        → equalInType i w (#FFDEFS A y) a b
                        → □· w (λ w' _ → FFDEFSeq y (equalInType i w' A) w' a b)
  equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {y} (eqt , eqi) = concl (#FFDEFS A y) (#FFDEFS A y) eqt eqi refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #FFDEFS A y → □· w' (λ w'' _ → FFDEFSeq y (equalInType u' w'' A) w'' a' b'))
            → T1 ≡ #FFDEFS A y → □· w (λ w' _ → FFDEFSeq y (equalInType u w' A) w' a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqQNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqTSQUASH (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqTCONST (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 rewrite eq1 =
          Mod.∀𝕎-□Func M aw eqi
            where
              aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms u w' (eqtA w' e')) w' a b → FFDEFSeq y (equalInType u w' A) w' a b)
              aw w1 e1 p =
                FFDEFSeq-ext-eq₀
                  {w1} {_} {_} {x1} {y} {a} {b} (sym (#FFDEFSinj2 {A} {y} {A1} {x1} (#compAllVal x tt)))
                  (λ a1 a2 ea → eqInType→equalInType (#FFDEFSinj1 {A} {y} {A1} {x1} (#compAllVal x tt)) (eqtA w1 e1) ea) p
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 rewrite eq1 = ⊥-elim (FFDEFSneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) (at : at□· x w' e' z)
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → FFDEFSeq y (equalInType u w'' A) w'' a b) e'))
          aw w1 e1 z at h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (ind {u} {w1} {T1} {T2} z h (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt a b)
              → T1 ≡ #FFDEFS A y → □· w (λ w' _ → FFDEFSeq y (equalInType i w' A) w' a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #FFDEFS A y → □· w (λ w' _ → FFDEFSeq y (equalInType i w' A) w' a b))
          ind eqt a b eqi



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



→equalInType-TNAT : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → TNATeq w' a b)
                    → equalInType i w #TNAT a b
→equalInType-TNAT i w a b j = eqTypesTNAT , j



equalInType-QNAT→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #QNAT a b
                     → □· w (λ w' _ → #weakMonEq w' a b)
equalInType-QNAT→ i w a b (eqt , eqi) =
  eqInType-⇛-QNAT (uni i) w #QNAT #QNAT a b (#compAllRefl #QNAT w) (#compAllRefl #QNAT w) eqt eqi



equalInType-TNAT→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #TNAT a b
                     → □· w (λ w' _ → TNATeq w' a b)
equalInType-TNAT→ i w a b (eqt , eqi) =
  eqInType-⇛-TNAT (uni i) w #TNAT #TNAT a b (#compAllRefl #TNAT w) (#compAllRefl #TNAT w) eqt eqi




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


eqTypesISECT← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w C D
                  → equalTypes i w (#ISECT A C) (#ISECT B D)
eqTypesISECT← {w} {i} {A} {B} {C} {D} eqt1 eqt2 =
  EQTISECT A C B D (#compAllRefl (#ISECT A C) w) (#compAllRefl (#ISECT B D) w)
           (eqTypes-mon (uni i) eqt1) (eqTypes-mon (uni i) eqt2)
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt1))
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt2))


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
                  → isType u w A
                  → isType u w B
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
                  → equalInType u w (#FUN A B) f g
equalInType-FUN {u} {w} {A} {B} {f} {g} ha hb i rewrite #FUN≡#PI A B =
  equalInType-PI (eqTypes-mon (uni u) ha) hb' eqi'
  where
    hb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ B ⌟))
    hb' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ B = eqTypes-mon (uni u) hb w1 e1

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
  equalInType-FUN ha eqTypesFALSE eqi
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
    eqi = □'-change₀ W M i (Mod.∀𝕎-□Func M aw i) aw'' (∀𝕎-□-□'₀ W M i aw')

-- Used to go through with just??? Mod.∀𝕎-□-□' M i aw'


eqTypes-change-level : (i j : univs) {w : 𝕎·} {T1 T2 : CTerm}
                       → i ≡ j
                       → eqTypes i w T1 T2
                       → eqTypes j w T1 T2
eqTypes-change-level i j {w} {T1} {T2} eqij eqt rewrite eqij = eqt


eqInType-↓U-uni : (i : ℕ) {w : 𝕎·} {T1 T2 : CTerm}
                  (eqt1 : eqTypes (uni (↓𝕃 i)) w T1 T2) (eqt2 : eqTypes (↓U (uni i)) w T1 T2)
                  {a b : CTerm}
                  → eqInType (uni (↓𝕃 i)) w eqt1 a b
                  → eqInType (↓U (uni i)) w eqt2 a b
eqInType-↓U-uni i {w} {T1} {T2} eqt1 eqt2 {a} {b} eqi rewrite ↓U-uni i =
  eqInType-extl1 T2 T2 eqt1 eqt2 eqi


eqInType-uni-↓U : (i : ℕ) {w : 𝕎·} {T1 T2 : CTerm}
                  (eqt1 : eqTypes (↓U (uni i)) w T1 T2) (eqt2 : eqTypes (uni (↓𝕃 i)) w T1 T2)
                  {a b : CTerm}
                  → eqInType (↓U (uni i)) w eqt1 a b
                  → eqInType (uni (↓𝕃 i)) w eqt2 a b
eqInType-uni-↓U i {w} {T1} {T2} eqt1 eqt2 {a} {b} eqi rewrite ↓U-uni i =
  eqInType-extl1 T2 T2 eqt1 eqt2 eqi


≡suc→↓U-uni≡ : (u n : ℕ) → u ≡ suc n → ↓U (uni u) ≡ uni n
≡suc→↓U-uni≡ u n equ rewrite equ | ↓U-uni (suc n) = refl


abstract
  equalInType-LIFT→ : (n : ℕ) (w : 𝕎·) (T a b : CTerm)
                      → equalInType (suc n) w (#LIFT T) a b
                      → equalInType n w T a b
  equalInType-LIFT→ n w T a b (eqt , eqi) = concl (suc n) (#LIFT T) (#LIFT T) eqt eqi refl refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → u' ≡ suc n → T1' ≡ #LIFT T → T2' ≡ #LIFT T → equalInType n w' T a' b')
            → u ≡ suc n → T1 ≡ #LIFT T → T2 ≡ #LIFT T → equalInType n w T a b
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind equ eq1 eq2 rewrite equ | eq1 | eq2 = ⊥-elim (LIFTneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind equ eq1 eq2 rewrite equ
        = equalInType-local (Mod.∀𝕎-□Func M aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → eqInType (↓U (uni (suc n))) w' (eqtA w' e') a b → equalInType n w' T a b)
          aw w1 e1 z =
            eqInType→equalInType {n} {w1} {T} {A1} {A2} {a} {b}
              (#LIFTinj {T} {A1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#LIFT T) T1 (sym eq1) tt))))
              (eqTypes-change-level (↓U (uni (suc n))) (uni n) {w1} {A1} {A2} (↓U-uni (suc n)) (eqtA w1 e1))
              (eqInType-uni-↓U (suc n) (eqtA w1 e1) (eqTypes-change-level (↓U (uni (suc n))) (uni n) {w1} {A1} {A2} (↓U-uni (suc n)) (eqtA w1 e1)) z)
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind equ eq1 eq2 =
        equalInType-local (Mod.∀𝕎-□'-□ M x aw eqi)
          where
            aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                                → (at : at□· x w' e' z)
                                → equalTerms u w' z a b
                                → equalInType n w' T a b)
            aw w' e' z at j = ind {u} {w'} {T1} {T2} z {a} {b} j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) equ eq1 eq2

      concl : (m : ℕ) (T1 T2 : CTerm) (eqt : equalTypes m w T1 T2) (eqi : equalTerms m w eqt a b)
              → m ≡ suc n → T1 ≡ #LIFT T → T2 ≡ #LIFT T → equalInType n w T a b
      concl m T1 T2 eqt eqi =
        equalTerms-ind
          (λ {m} {w} {T1} {T2} eqt {a} {b} eqi → m ≡ suc n → T1 ≡ #LIFT T → T2 ≡ #LIFT T → equalInType n w T a b)
          ind eqt a b eqi


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



abstract
  equalInType-PI→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                    → equalInType u w (#PI A B) f g
                    → isFam u w A B (#APPLY f) (#APPLY g)
  equalInType-PI→ {u} {w} {A} {B} {f} {g} (eqt , eqi) = concl (#PI A B) (#PI A B) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #PI A B → T2' ≡ #PI A B → isFam u' w' A B (#APPLY a') (#APPLY b'))
            → T1 ≡ #PI A B → T2 ≡ #PI A B → isFam u w A B (#APPLY a) (#APPLY b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        ≡CTerm→eqTypes
          (sym (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)))
          (sym (#PIinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt)))
          (eqta w (⊑-refl· w)) ,
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
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTSQUASH (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTCONST (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {f} {g} eqi ind eq1 eq2 =
        isFam-local {u} {w} {A} {B} {#APPLY f} {#APPLY g} (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → at□· x w' e' z
                              → equalTerms u w' z f g
                              → isFam u w' A B (#APPLY f) (#APPLY g))
          aw w' e' z at j = ind {u} {w'} {T1} {T2} z {f} {g} j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes u w T1 T2) (eqi : equalTerms u w eqt f g)
              → T1 ≡ #PI A B → T2 ≡ #PI A B → isFam u w A B (#APPLY f) (#APPLY g)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {u} {w} {T1} {T2} eqt {f} {g} eqi → T1 ≡ #PI A B → T2 ≡ #PI A B → isFam u w A B (#APPLY f) (#APPLY g))
          ind eqt f g eqi



abstract
  equalInType-SET→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                     → equalInType u w (#SET A B) f g
                     → □· w (λ w' _ → SETeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) f g)
  equalInType-SET→ {u} {w} {A} {B} {f} {g} (eqt , eqi) = concl (#SET A B) (#SET A B) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #SET A B → T2' ≡ #SET A B
                → □· w' (λ w'' _ → SETeq (equalInType u' w'' A) (λ a₁ b₁ ea → equalInType u' w'' (sub0 a₁ B)) a' b'))
            → T1 ≡ #SET A B → T2 ≡ #SET A B → □· w (λ w' _ → SETeq (equalInType u w' A) (λ a₁ b₁ ea → equalInType u w' (sub0 a₁ B)) a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms u w' (eqta w' e')) (λ a1 a2 eqa → equalTerms u w' (eqtb w' e' a1 a2 eqa)) f g
                             → SETeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) f g)
          aw w' e' (b , ea , eb) = b , ea' , eb'
            where
              ea' : equalInType u w' A f g
              ea' = eqInType→equalInType {u} {w'} {A} {A1} {A2} (#SETinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqta w' e') ea

              eb' : equalInType u w' (sub0 f B) b b
              eb' = eqInType→equalInType {u} {w'} {sub0 f B} {sub0 f B1} {sub0 g B2} (→≡sub0 (#SETinj2 {A} {B} {A1} {B1} (#compAllVal x tt))) (eqtb w' e' f g ea) eb
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {f} {g} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SETneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {f} {g} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → at□· x w' e' z
                              → equalTerms u w' z f g
                              → □· w' (↑wPred' (λ w'' e → SETeq (equalInType u w'' A) (λ a b ea → equalInType u w'' (sub0 a B)) f g) e'))
          aw w' e' z at j = Mod.∀𝕎-□Func M (λ w1 e1 h z → h) (ind {u} {w'} {T1} {T2} z {f} {g} j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes u w T1 T2) (eqi : equalTerms u w eqt f g)
              → T1 ≡ #SET A B → T2 ≡ #SET A B → □· w (λ w' _ → SETeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) f g)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {u} {w} {T1} {T2} eqt {f} {g} eqi → T1 ≡ #SET A B → T2 ≡ #SET A B → □· w (λ w' _ → SETeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) f g))
          ind eqt f g eqi


abstract
  equalInType-SQUASH-aux→ : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                            (eqt : isType n w (#SET #TRUE ⌞ A ⌟))
                            → equalTerms n w eqt a b
                            → □· w (λ w' _ → Σ CTerm (λ t → equalInType n w' A t t))
  equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} eqt eqi =
    Mod.∀𝕎-□Func M aw (equalInType-SET→ {n} {w} {#TRUE} {⌞ A ⌟} {a} {b} (eqt , eqi))
    where
      aw : ∀𝕎 w (λ w' e' → SETeq (equalInType n w' #TRUE) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ ⌞ A ⌟)) a b
                          → Σ CTerm (λ t → equalInType n w' A t t))
      aw w1 e1 (x , ea , eb) rewrite sub0⌞⌟ a A = x , eb



abstract
  equalInType-SQUASH→ : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                         → equalInType n w (#SQUASH A) a b
                         → □· w (λ w' _ → inhType n w' A)
  equalInType-SQUASH→ {n} {w} {A} {a} {b} (eqt , eqi) rewrite #SQUASH≡#SET A = equalInType-SQUASH-aux→ eqt eqi



abstract
  equalInType-ISECT→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                          → equalInType n w (#ISECT A B) a b
                          → □· w (λ w' _ → ISECTeq (equalInType n w' A) (equalInType n w' B) a b)
  equalInType-ISECT→ {n} {w} {A} {B} {a} {b} (eqt , eqi) = concl (#ISECT A B) (#ISECT A B) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #ISECT A B → T2' ≡ #ISECT A B
                → □· w' (λ w'' _ → ISECTeq (equalInType u' w'' A) (equalInType u' w'' B) a' b'))
            → T1 ≡ #ISECT A B → T2 ≡ #ISECT A B → □· w (λ w' _ → ISECTeq (equalInType u w' A) (equalInType u w' B) a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → ISECTeq (equalTerms u w' (eqtA w' e')) (equalTerms u w' (eqtB w' e')) a b
                              → ISECTeq (equalInType u w' A) (equalInType u w' B) a b)
          aw w' e' (u₁ , u₂) =
            (eqInType→equalInType (#ISECTinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtA w' e') u₁) ,
            (eqInType→equalInType (#ISECTinj2 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtB w' e') u₂)
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → at□· x w' e' z
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → ISECTeq (equalInType u w'' A) (equalInType u w'' B) a b) e'))
          aw w' e' z at i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) j
            where
              j : □· w' (λ w' _ → ISECTeq (equalInType u w' A) (equalInType u w' B) a b)
              j = ind {u} {w'} {T1} {T2} z {a} {b} i (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes n w T1 T2) (eqi : equalTerms n w eqt a b)
              → T1 ≡ #ISECT A B → T2 ≡ #ISECT A B → □· w (λ w' _ → ISECTeq (equalInType n w' A) (equalInType n w' B) a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {n} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #ISECT A B → T2 ≡ #ISECT A B → □· w (λ w' _ → ISECTeq (equalInType n w' A) (equalInType n w' B) a b))
          ind eqt a b eqi


abstract
  equalInType-EQ→ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                    → equalInType u w (#EQ a b A) f g
                    → □· w (λ w' _ → EQeq a b (equalInType u w' A) w' f g)
  equalInType-EQ→ {u} {w} {a} {b} {A} {f} {g} eqi = if-equalInType-EQ u w A a b f g eqi



abstract
  ¬equalInType-FALSE : {w : 𝕎·} {i : ℕ} {a b : CTerm} → ¬ equalInType i w #FALSE a b
  ¬equalInType-FALSE {w} {i} {a} {b} eqi =
    lower {0ℓ} {lsuc(L)} (Mod.□-const M (Mod.∀𝕎-□Func M aw eqi1))
    where
      aw : ∀𝕎 w (λ w' e' → equalInType i w' #NAT #N0 #N1 → Lift (lsuc L) ⊥)
      aw w' e' ea = Mod.□-const M (Mod.∀𝕎-□Func M aw' z)
        where
          z : □· w' (λ w'' e → NATeq w'' #N0 #N1)
          z = eqInType-⇛-NAT (uni i) w' #NAT #NAT #N0 #N1 (#compAllRefl #NAT w') (#compAllRefl #NAT w') (fst ea) (snd ea)

          aw' : ∀𝕎 w' (λ w'' e'' → NATeq w'' #N0 #N1 → Lift (lsuc(L)) ⊥)
          aw' w'' e'' s = lift (¬#strongMonEq-N0-N1 w'' s)

      eqi1 : □· w (λ w' _ → equalInType i w' #NAT #N0 #N1)
      eqi1 = equalInType-EQ→ eqi


abstract
  equalInType-UNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                          → equalInType n w (#UNION A B) a b
                          → □· w (λ w' _ → UNIONeq (equalInType n w' A) (equalInType n w' B) w' a b)
  equalInType-UNION→ {n} {w} {A} {B} {a} {b} (eqt , eqi) = concl (#UNION A B) (#UNION A B) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #UNION A B → T2' ≡ #UNION A B
                → □· w' (λ w'' _ → UNIONeq (equalInType u' w'' A) (equalInType u' w'' B) w'' a' b'))
            → T1 ≡ #UNION A B → T2 ≡ #UNION A B → □· w (λ w' _ → UNIONeq (equalInType u w' A) (equalInType u w' B) w' a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
          where
            aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms u w' (eqtA w' e')) (equalTerms u w' (eqtB w' e')) w' a b
                                → UNIONeq (equalInType u w' A) (equalInType u w' B) w' a b)
            aw w' e' (y , z , inj₁ (c₁ , c₂ , p)) = y , z , inj₁ (c₁ , c₂ , eqInType→equalInType (#UNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtA w' e') p)
            aw w' e' (y , z , inj₂ (c₁ , c₂ , p)) = y , z , inj₂ (c₁ , c₂ , eqInType→equalInType (#UNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtB w' e') p)
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqQTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → at□· x w' e' z
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → UNIONeq (equalInType u w'' A) (equalInType u w'' B) w'' a b) e'))
          aw w' e' z at i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) j
            where
              j : □· w' (λ w' _ → UNIONeq (equalInType u w' A) (equalInType u w' B) w' a b)
              j = ind {u} {w'} {T1} {T2} z {a} {b} i (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes n w T1 T2) (eqi : equalTerms n w eqt a b)
              → T1 ≡ #UNION A B → T2 ≡ #UNION A B → □· w (λ w' _ → UNIONeq (equalInType n w' A) (equalInType n w' B) w' a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {n} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #UNION A B → T2 ≡ #UNION A B → □· w (λ w' _ → UNIONeq (equalInType n w' A) (equalInType n w' B) w' a b))
          ind eqt a b eqi


abstract
  equalInType-QTUNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                          → equalInType n w (#QTUNION A B) a b
                          → □· w (λ w' _ → QTUNIONeq (equalInType n w' A) (equalInType n w' B) w' a b)
  equalInType-QTUNION→ {n} {w} {A} {B} {a} {b} (eqt , eqi) = concl (#QTUNION A B) (#QTUNION A B) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {a b : CTerm} (eqi : equalTerms u w eqt a b)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {a' b' : CTerm} (eqi' : equalTerms u' w' eqt' a' b')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #QTUNION A B → T2' ≡ #QTUNION A B
                → □· w' (λ w'' _ → QTUNIONeq (equalInType u' w'' A) (equalInType u' w'' B) w'' a' b'))
            → T1 ≡ #QTUNION A B → T2 ≡ #QTUNION A B → □· w (λ w' _ → QTUNIONeq (equalInType u w' A) (equalInType u w' B) w' a b)
      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqQNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
          where
            aw : ∀𝕎 w (λ w' e' → QTUNIONeq (equalTerms u w' (eqtA w' e')) (equalTerms u w' (eqtB w' e')) w' a b
                                → QTUNIONeq (equalInType u w' A) (equalInType u w' B) w' a b)
            aw w' e' (y , z , inj₁ (c₁ , c₂ , p)) = y , z , inj₁ (c₁ , c₂ , eqInType→equalInType (#QTUNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtA w' e') p)
            aw w' e' (y , z , inj₂ (c₁ , c₂ , p)) = y , z , inj₂ (c₁ , c₂ , eqInType→equalInType (#QTUNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtB w' e') p)
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqTSQUASH (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqTCONST (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i p x x₁) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqUNIV (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {a} {b} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (QTUNIONneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {a} {b} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → at□· x w' e' z
                              → equalTerms u w' z a b
                              → □· w' (↑wPred' (λ w'' e → QTUNIONeq (equalInType u w'' A) (equalInType u w'' B) w'' a b) e'))
          aw w' e' z at i = Mod.∀𝕎-□Func M (λ w'' e'' h k → h) j
            where
              j : □· w' (λ w' _ → QTUNIONeq (equalInType u w' A) (equalInType u w' B) w' a b)
              j = ind {u} {w'} {T1} {T2} z {a} {b} i (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes n w T1 T2) (eqi : equalTerms n w eqt a b)
              → T1 ≡ #QTUNION A B → T2 ≡ #QTUNION A B → □· w (λ w' _ → QTUNIONeq (equalInType n w' A) (equalInType n w' B) w' a b)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {n} {w} {T1} {T2} eqt {a} {b} eqi → T1 ≡ #QTUNION A B → T2 ≡ #QTUNION A B → □· w (λ w' _ → QTUNIONeq (equalInType n w' A) (equalInType n w' B) w' a b))
          ind eqt a b eqi



equalInType-FUN→ : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                    → equalInType u w (#FUN A B) f g
                    → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
equalInType-FUN→ {u} {w} {A} {B} {f} {g} eqi rewrite #FUN≡#PI A B = z2
  where
    z1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ ⌞ B ⌟) (#APPLY f a₁) (#APPLY g a₂))
    z1 = snd (snd (equalInType-PI→ eqi))

    z2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
    z2 w' e' a₁ a₂ ea = ≡CTerm→equalInType (sub0⌞⌟ a₁ B ) (z1 w' e' a₁ a₂ ea)



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



equalInType-W : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                  → □· w (λ w' _ → Weq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
                  → equalInType u w (#WT A B) f g
equalInType-W {u} {w} {A} {B} {f} {g} ha hb eqi =
  eqTypesW← ha hb , Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → Weq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g
                       → Weq (eqInType (uni u) w' (ha w' e')) (λ a1 a2 eqa → eqInType (uni u) w' (equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = weq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → equalInType u w1 A a b → eqInType (uni u) w1 (ha w1 e1) a b
        ea1 a b q = equalInType→eqInType {u} {w1} {A} {A} {A} refl {ha w1 e1} q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea1 : equalInType u w1 A a b)
              (ea2 : eqInType (uni u) w1 (ha w1 e1) a b)
              → eqInType (uni u) w1 (equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w1 e1 a b ea2) f₁ g₁
              → equalInType u w1 (sub0 a B) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q =
          eqInType→equalInType
            {u} {w1} {sub0 a B} {sub0 a B} {sub0 b B} {f₁} {g₁} refl
            (equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w1 e1 a b ea3) q

 {--(λ w' e' (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) →
      a₁ , a₂ , b₁ , b₂ ,
      equalInType→eqInType {u} {w'} {A} {A} {A} refl {ha w' e'} ea ,
      c₁ , c₂ ,
      equalInType→eqInType
        {u} {w'} {sub0 a₁ B} {sub0 a₁ B} {sub0 a₂ B} refl
        {equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w' e' a₁ a₂ (equalInType→eqInType {u} {w'} {A} {A} {A} refl {ha w' e'} ea)}
        eb)--}




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
