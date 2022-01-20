\begin{code}
{-# OPTIONS --rewriting #-}

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
open import getChoice
open import newChoice
open import freeze
open import progress
--open import choiceBar


module lem {L : Level} (W : PossibleWorlds {L})
           (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
--           (CB : ChoiceBar W C G N F P E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
--open import choiceBarDef(W)(C)(G)(N)(F)(P)(E)(CB)
open import computation(W)(C)(G)
open import bar(W)(C)(G)(N)(F)(P)
open import barI(W)(C)(G)(N)(F)(P)
open import theory(W)(C)(G)(N)(F)(P)(E)
open import props0(W)(C)(G)(N)(F)(P)(E)
open import ind2(W)(C)(G)(N)(F)(P)(E)

open import type_sys_props_nat(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_qnat(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_lt(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_qlt(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_free(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_pi(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_sum(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_set(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_eq(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_union(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_tsquash(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_ffdefs(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_lift(W)(C)(G)(N)(F)(P)(E)

open import props1(W)(C)(G)(N)(F)(P)(E)
open import props2(W)(C)(G)(N)(F)(P)(E)
open import props3(W)(C)(G)(N)(F)(P)(E)
open import lem_props(W)(C)(G)(N)(F)(P)(E)
\end{code}




\begin{code}[hide]
-- MOVE to props3
→equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → inbar w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#UNION A B) a b
→equalInType-UNION {n} {w} {A} {B} {a} {b} isa isb i = eqTypesUNION← isa isb , Bar.∀𝕎-inBarFunc barI aw i
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType n w' A x y
                            ⊎ a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType n w' B x y))
                       → UNIONeq (eqInType (uni n) w' (eqTypes-mon (uni n) isa w' e')) (eqInType (uni n) w' (eqTypes-mon (uni n) isb w' e')) w' a b)
    aw w1 e1 (x , y , inj₁ (c₁ , c₂ , ea)) = x , y , inj₁ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isa w1 e1} ea)
    aw w1 e1 (x , y , inj₂ (c₁ , c₂ , ea)) = x , y , inj₂ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isb w1 e1} ea)


-- MOVE to theory
INHT : Set(lsuc(lsuc(L)))
INHT = (w : 𝕎·) (T : CTerm) → Set(lsuc(L))


-- MOVE to theory
inhType : (u : ℕ) → INHT
inhType u w T = Σ CTerm (λ t → ∈Type u w T t)


equalInType-NEG-inh : {u : ℕ} {w : 𝕎·} {A : CTerm}
                      → ∀𝕎 w (λ w' _ → isType u w' A)
                      → ∀𝕎 w (λ w' _ → ¬ inhType u w' A)
                      → inhType u w (#NEG A)
equalInType-NEG-inh {u} {w} {A} h q = #lamAX , equalInType-NEG h aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
    aw w1 e1 a₁ a₂ ea = q w1 e1 (a₁ , equalInType-refl ea)


classical : (w : 𝕎·) {n i : ℕ} (p : i < n) → member w (#LEM p) #lamAX
classical w {n} {i} p rewrite #LEM≡#PI p = n , equalInType-PI p1 p2 p3
  where
    -- p1 and p2 prove that LEM is a type
    p1 : ∀𝕎 w (λ w' _ → isType n w' (#UNIV i))
    p1 w1 _ = eqTypesUniv w1 n i p

    p2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' (#UNIV i) a₁ a₂)
                       → equalTypes n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                                          (sub0 a₂ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))))
    p2 w1 e1 a₁ a₂ ea =
      ≡CTerm→eqTypes (sym (sub0-#[0]SQUASH p a₁))
                      (sym (sub0-#[0]SQUASH p a₂))
                      (eqTypesSQUASH← (eqTypesUNION← (equalInType→equalTypes p w1 a₁ a₂ ea)
                                                       (eqTypesNEG← (equalInType→equalTypes p w1 a₁ a₂ ea))))

    -- now we prove that it is inhabited
    p3 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#UNIV i) a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                                           (#APPLY #lamAX a₁) (#APPLY #lamAX a₂))
    p3 w1 e1 a₁ a₂ ea =
      ≡CTerm→equalInType
        (sym (sub0-#[0]SQUASH p a₁))
        (→equalInType-SQUASH (inbar-APPLY-lamAX a₁) (inbar-APPLY-lamAX a₂) p4)
      where
        p6 : inbar w1 (λ w' _ → inhType n w' (#↑T p a₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType n w'' (#↑T p a₁)))
        p6 = {!!}

        p5 : inbar w1 (λ w' _ → inhType n w' (#↑T p a₁) ⊎ inhType n w' (#NEG (#↑T p a₁)))
        p5 = Bar.∀𝕎-inBarFunc barI aw p6
          where
            aw : ∀𝕎 w1 (λ w' e' → (inhType n w' (#↑T p a₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType n w'' (#↑T p a₁)))
                                 → (inhType n w' (#↑T p a₁) ⊎ inhType n w' (#NEG (#↑T p a₁))))
            aw w2 e2 (inj₁ i) = inj₁ i
            aw w2 e2 (inj₂ i) = inj₂ (equalInType-NEG-inh (λ w3 e3 → equalInType→equalTypes p w3 a₁ a₁ (equalInType-refl (equalInType-mon ea w3 (⊑-trans· e2 e3)))) i)

        p4 : inbar w1 (λ w' _ → Σ CTerm (λ t → ∈Type n w' (#UNION (#↑T p a₁) (#NEG (#↑T p a₁))) t))
        p4 = Bar.∀𝕎-inBarFunc barI aw p5
          where
            aw : ∀𝕎 w1 (λ w' e' → inhType n w' (#↑T p a₁) ⊎ inhType n w' (#NEG (#↑T p a₁))
                                →  Σ CTerm (λ t → ∈Type n w' (#UNION (#↑T p a₁) (#NEG (#↑T p a₁))) t))
            aw w2 e2 (inj₁ (t , h)) = #INL t , →equalInType-UNION (equalInType→equalTypes p w2 a₁ a₁ (equalInType-refl (equalInType-mon ea w2 e2)))
                                                                   (eqTypesNEG← (equalInType→equalTypes p w2 a₁ a₁ (equalInType-refl (equalInType-mon ea w2 e2))))
                                                                   (Bar.∀𝕎-inBar barI (λ w3 e3 → t , t , inj₁ (#compAllRefl (#INL t) w3 , #compAllRefl (#INL t) w3 , (equalInType-mon h w3 e3))))
            aw w2 e2 (inj₂ (t , h)) = #INR t , →equalInType-UNION (equalInType→equalTypes p w2 a₁ a₁ (equalInType-refl (equalInType-mon ea w2 e2)))
                                                                   (eqTypesNEG← (equalInType→equalTypes p w2 a₁ a₁ (equalInType-refl (equalInType-mon ea w2 e2))))
                                                                   (Bar.∀𝕎-inBar barI (λ w3 e3 → t , t , inj₂ (#compAllRefl (#INR t) w3 , #compAllRefl (#INR t) w3 , (equalInType-mon h w3 e3))))


\end{code}[hide]
