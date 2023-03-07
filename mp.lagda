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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import exBar
open import mod


module mp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
          (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
          (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
          (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
          (F : Freeze {L} W C K P G N)
          (E : Extensionality 0ℓ (lsuc(lsuc(L))))
          (CB : ChoiceBar W M C K P G X N V F E)
          (EB : ExBar W M)
          (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import exBarDef(W)(M)(EB)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



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


-- This is a simple unfolding of what it means to be a member of (#MP-left f)
equalInType-#MP-left→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                         → ∈Type i w #NAT!→BOOL f
                         → equalInType i w (#MP-left f) a₁ a₂
                         → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                                           → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                                           → ⊥)
                                          → ⊥)
equalInType-#MP-left→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh
    a∈ w1 e1
    (#AX , equalInType-PI
             (λ w' _ → isTypeNAT!)
             (→equalTypes-#PI-NEG-ASSERT₂-body (equalInType-refl (equalInType-mon f∈ w1 e1)))
             λ w2 e2 n₁ n₂ n∈ →
                 ≡CTerm→equalInType
                   (sym (sub0-NEG-ASSERT₂-APPLY n₁ f))
                   (equalInType-NEG
                     (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ (equalInType-refl f∈) w2 (⊑-trans· e1 e2) n₁ n₁ (equalInType-refl n∈)))
                     λ w3 e3 b₁ b₂ q → h w3 (⊑-trans· e2 e3) n₁ n₂ (equalInType-mon n∈ w3 e3) (b₁ , equalInType-refl q)))


-- This is classically equivalent to equalInType-#MP-left→
equalInType-#MP-left→2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL f
                          → equalInType i w (#MP-left f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∃𝕎 w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂
                                                            → equalInType i w' #NAT! n₁ n₂
                                                             × inhType i w' (#ASSERT₂ (#APPLY f n₁))))))
equalInType-#MP-left→2 i w f a₁ a₂ f∈ a∈ w1 e1 =
  h2 (EM {∃𝕎 w1 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂ × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))})
  where
    h1 : ∀𝕎 w1 (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                          → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                          → ⊥) → ⊥
    h1 = equalInType-#MP-left→ i w f a₁ a₂ f∈ a∈ w1 e1

    h2 : Dec (∃𝕎 w1 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂
                             → equalInType i w' #NAT! n₁ n₂
                              × inhType i w' (#ASSERT₂ (#APPLY f n₁))))))
         → ∃𝕎 w1 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂
                          → equalInType i w' #NAT! n₁ n₂
                           × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
    h2 (yes p) = p
    h2 (no p) = ⊥-elim (h1 (λ w2 e2 n₁ n₂ n∈ inh → p (w2 , e2 , n₁ , n₂ , n∈ , inh)))


∀𝕎∃𝕎-func : {w : 𝕎·} {f g : wPred w}
              → ∀𝕎 w (λ w1 e1 → f w1 e1 → g w1 e1)
              → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (↑wPred f e1))
              → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (↑wPred g e1))
∀𝕎∃𝕎-func {w} {f} {g} h q w1 e1 =
  fst q' , fst (snd q') , h (fst q') (⊑-trans· e1 (fst (snd q'))) (snd (snd q'))
  where
    q' : ∃𝕎 w1 (↑wPred f e1)
    q' = q w1 e1


MPvalid : (w : 𝕎·) → member w #MP #lamAX
MPvalid w rewrite #MP≡#PI = n , equalInType-PI {n} {w} {#NAT!→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right} p1 p2 p3
  where
    n : ℕ
    n = 1

    p1 : ∀𝕎 w (λ w' _ → isType n w' #NAT!→BOOL)
    p1 w1 e1 = isType-#NAT!→BOOL w1 n

    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' #NAT!→BOOL f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp f₁))
        (sym (sub0-fun-mp f₂))
        (eqTypesFUN← (→equalTypes-#MP-left f∈) (→equalTypes-#MP-right f∈))

    p3 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' #NAT!→BOOL f₁ f₂
                       → equalInType n w' (sub0 f₁ (#[0]FUN #[0]MP-left #[0]MP-right)) (#APPLY #lamAX f₁) (#APPLY #lamAX f₂))
    p3 w1 e1 f₁ f₂ f∈ =
      →≡equalInType
        (sym (sub0-fun-mp f₁))
        (equalInType-FUN
          (TEQrefl-equalTypes n w1 _ _ (→equalTypes-#MP-left f∈))
          (TEQrefl-equalTypes n w1 _ _ (→equalTypes-#MP-right f∈))
          p4)
      where
        p4 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#MP-left f₁) a₁ a₂
                            → equalInType n w' (#MP-right f₁) (#APPLY (#APPLY #lamAX f₁) a₁) (#APPLY (#APPLY #lamAX f₂) a₂))
        p4 w2 e2 a₁ a₂ a∈ = →equalInType-SQUASH p5
          where
            p7 : ∀𝕎 w2 (λ w' _ → ∃𝕎 w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂
                                                  → equalInType n w' #NAT! n₁ n₂
                                                   × inhType n w' (#ASSERT₂ (#APPLY f₁ n₁))))))
            p7 = equalInType-#MP-left→2 n w2 f₁ a₁ a₂ (equalInType-refl (equalInType-mon f∈ w2 e2)) a∈

            aw : ∀𝕎 w2 (λ w3 e3 → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w3 #NAT! n₁ n₂ × inhType n w3 (#ASSERT₂ (#APPLY f₁ n₁))))
                                → □· w3 (↑wPred (λ w' _ → Σ CTerm (λ t → ∈Type n w' (#SUM-ASSERT₂ f₁) t)) e3))
            aw w3 e3 (n₁ , n₂ , n∈ , (t , inh)) =
              Mod.∀𝕎-□ M aw1
              where
               aw1 : ∀𝕎 w3 (↑wPred (λ w' _ → Σ CTerm (λ t → ∈Type n w' (#SUM-ASSERT₂ f₁) t)) e3)
               aw1 w4 e4 =
                 #PAIR n₁ t ,
                 equalInType-SUM
                   (λ w' _ → isTypeNAT!)
                   (λ w' e' a₁ a₂ a∈ → →≡equalTypes (sym (sub0-ASSERT₂-APPLY a₁ f₁)) (sym (sub0-ASSERT₂-APPLY a₂ f₁)) (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ (equalInType-refl f∈) w' (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e'))) a₁ a₂ a∈)))
                   (Mod.∀𝕎-□ M aw2)
                 where
                   aw2 : ∀𝕎 w4 (λ w' _ → SUMeq (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                   aw2 w5 e5 =
                     n₁ , n₁ , t , t , equalInType-refl (equalInType-mon n∈ w5 (⊑-trans· e4 e5)) ,
                     #compAllRefl (#PAIR n₁ t) w5 ,
                     #compAllRefl (#PAIR n₁ t) w5 ,
                     ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f₁)) (equalInType-mon inh w5 (⊑-trans· e4 e5))

            p6 : ∀𝕎 w2 (λ w3 e3 → ∃𝕎 w3 (λ w4 e4
                    → □· w4 (↑wPred (λ w' _ → Σ CTerm (λ t → ∈Type n w' (#SUM-ASSERT₂ f₁) t)) (⊑-trans· e3 e4))))
            p6 = ∀𝕎∃𝕎-func aw p7

            p5 : □· w2 (λ w' _ → Σ CTerm (λ t → ∈Type n w' (#SUM-ASSERT₂ f₁) t))
            p5 = ∀∃𝔹· (λ w' e1 e2 h → h) p6

\end{code}[hide]
