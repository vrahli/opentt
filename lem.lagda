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
open import Axiom.ExcludedMiddle


open import util
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import exBar


module lem {L : Level} (W : PossibleWorlds {L})
           (C : Choice) (G : GetChoice {L} W C) (X : ChoiceExt C) (N : NewChoice {L} W C G)
           (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
           (EM : ExcludedMiddle (lsuc(L)))
           (EB : ExBar W C G N F P E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import choiceExtDef(W)(C)(G)(X)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
open import exBarDef(W)(C)(G)(N)(F)(P)(E)(EB)
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
open import lem_props(W)(C)(G)(X)(N)(F)(P)(E)
\end{code}




\begin{code}[hide]
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
      ≡CTerm→eqTypes (sym (sub0-#[0]SQUASH-LEM p a₁))
                      (sym (sub0-#[0]SQUASH-LEM p a₂))
                      (eqTypesSQUASH← (eqTypesUNION← (equalInType→equalTypes p w1 a₁ a₂ ea)
                                                       (eqTypesNEG← (equalInType→equalTypes p w1 a₁ a₂ ea))))

    -- now we prove that it is inhabited
    p3 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#UNIV i) a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                                           (#APPLY #lamAX a₁) (#APPLY #lamAX a₂))
    p3 w1 e1 a₁ a₂ ea =
      ≡CTerm→equalInType
        (sym (sub0-#[0]SQUASH-LEM p a₁))
        (→equalInType-SQUASH (inbar-APPLY-lamAX a₁) (inbar-APPLY-lamAX a₂) p4)
      where
        p6 : inbar w1 (λ w' _ → inhType n w' (#↑T p a₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType n w'' (#↑T p a₁)))
        p6 = ∀∃𝔹· (λ w' e1 e2 h → h) aw
          where
            aw : ∀𝕎 w1 (λ w2 e2 → ∃𝕎 w2 (λ w3 e3 → inbar w3 (λ w' e → inhType n w' (#↑T p a₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType n w'' (#↑T p a₁)))))
            aw w2 e2 = cc (EM {∃𝕎 w2 (λ w3 e3 → inhType n w3 (#↑T p a₁))})
              where
                cc : Dec (∃𝕎 w2 (λ w3 e3 → inhType n w3 (#↑T p a₁)))
                     → ∃𝕎 w2 (λ w3 e3 → inbar w3 (λ w' e → inhType n w' (#↑T p a₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType n w'' (#↑T p a₁))))
                cc (no ¬p) = w2 , ⊑-refl· _ , Bar.∀𝕎-inBar barI (λ w4 e4 → inj₂ (λ w5 e5 z → ¬p (w5 , ⊑-trans· e4 e5 , z)))
                cc (yes (w3 , e3 , p)) = w3 , e3 , Bar.∀𝕎-inBar barI (λ w4 e4 → inj₁ (inhType-mon e4 p))

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



-- We now prove that open bars satisfy the ExBar property
∀∃𝔹-open : {w : 𝕎·} {f : wPred w} → wPredExtIrr f → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → inOpenBar w2 (↑wPred f (⊑-trans· e1 e2)))) → inOpenBar w f
∀∃𝔹-open {w} {f} ext h w1 e1 =
  w3 ,
  ⊑-trans· e2 e3 ,
  λ w4 e4 z → ext w4 (⊑-trans· (⊑-trans· e1 e2) (⊑-trans· e3 e4)) z (h3 w4 e4 (⊑-trans· e3 e4))
  where
    w2 : 𝕎·
    w2 = fst (h w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (h w1 e1))

    h2 : inOpenBar w2 (↑wPred f (⊑-trans· e1 e2))
    h2 = snd (snd (h w1 e1))

    w3 : 𝕎·
    w3 = fst (h2 w2 (⊑-refl· _))

    e3 : w2 ⊑· w3
    e3 = fst (snd (h2 w2 (⊑-refl· _)))

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w2 ⊑· w4) → f w4 (⊑-trans· (⊑-trans· e1 e2) z))
    h3 = snd (snd (h2 w2 (⊑-refl· _)))

\end{code}[hide]
