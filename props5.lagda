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


module props5 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_m(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)



-- appends a new value
APPEND : Term → Term → Term
APPEND l x =
  SPREAD l (PAIR (SUC (VAR 0))
                 (LAMBDA (IFLT (VAR 0)
                               (VAR 1)
                               (APPLY (VAR 2) (VAR 0))
                               (shiftUp 0 (shiftUp 0 (shiftUp 0 x))))))

{--
  PAIR (SUC k) (LAMBDA (IFLT (VAR 0) (shiftUp 0 k) (APPLY (shiftUp 0 f) (VAR 0)) (shiftUp 0 x)))
  where
    k : Term
    k = FST l

    f : Term
    f = SND l
--}


-- empty list (of numbers)
EMPTY : Term
EMPTY = PAIR (NUM 0) (LAMBDA (NUM 0))


PROD : Term → Term → Term
PROD a b = SUM a (shiftUp 0 b)


#PROD : CTerm → CTerm → CTerm
#PROD a b = ct (PROD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # PROD ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | #shiftUp 0 b | lowerVars-fvars-CTerm≡[] b = refl


#PROD≡#SUM : (A B : CTerm) → #PROD A B ≡ #SUM A ⌞ B ⌟
#PROD≡#SUM A B = CTerm≡ e
  where
    e : PROD ⌜ A ⌝ ⌜ B ⌝ ≡ SUM ⌜ A ⌝ ⌜ B ⌝
    e rewrite #shiftUp 0 B = refl


LIST : Term → Term
LIST A = PROD NAT (FUN NAT A)


#LIST : CTerm → CTerm
#LIST A = #PROD #NAT (#FUN #NAT A)


PRODeq : (eqa eqb : per) → wper
PRODeq eqa eqb w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    eqa a1 a2
    × eqb b1 b2
    × f #⇛ (#PAIR a1 b1) at w
    × g #⇛ (#PAIR a2 b2) at w))))


equalInType-PROD : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                  → isType u w A
                  → isType u w B
                  → □· w (λ w' _ → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g)
                  → equalInType u w (#PROD A B) f g
equalInType-PROD {u} {w} {A} {B} {f} {g} ha hb eqi =
  ≡CTerm→equalInType (sym (#PROD≡#SUM A B)) (equalInType-SUM ha' hb' eqi')
  where
    ha' : ∀𝕎 w (λ w' _ → isType u w' A)
    ha' w1 e1 = eqTypes-mon (uni u) ha w1 e1

    hb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ B ⌟))
    hb' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ B = eqTypes-mon (uni u) hb w1 e1

    aw : ∀𝕎 w (λ w' e' → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g
                       → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a (CTerm→CTerm0 B))) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , ea , eb , c1 , c2) = a1 , a2 , b1 , b2 , ea , c1 , c2 , eb'
      where
        eb' : equalInType u w1 (sub0 a1 (CTerm→CTerm0 B)) b1 b2
        eb' rewrite sub0⌞⌟ a1 B = eb

    eqi' : □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a ⌞ B ⌟)) w' f g)
    eqi' = Mod.∀𝕎-□Func M aw eqi


equalInType-PROD→ : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                     → equalInType u w (#PROD A B) f g
                     → □· w (λ w' _ → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g)
equalInType-PROD→ {u} {w} {A} {B} {f} {g} eqi =
  Mod.∀𝕎-□Func M aw (equalInType-SUM→ {u} {w} {A} {⌞ B ⌟} {f} {g} (≡CTerm→equalInType (#PROD≡#SUM A B) eqi))
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a (CTerm→CTerm0 B))) w' f g
                        → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , ea , c1 , c2 , eb) rewrite sub0⌞⌟ a1 B = a1 , a2 , b1 , b2 , ea , eb , c1 , c2

\end{code}
