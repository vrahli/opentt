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
open import mod


module mp_search {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
                 (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
                 (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                 (F : Freeze {L} W C K P G N)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (CB : ChoiceBar W M C K P G X N V F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms3(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)




-- f is a function in #NAT!→BOOL
-- We're defining here the infinite search: fix(λR.λn.if f(n) then n else R(suc(n)))0
-- The closed version #infSearch is below
infSearch : Term → Term
infSearch f =
  -- 1 is the recursive call and 0 is the number
  APPLY
    (FIX (LAMBDA (LAMBDA (ITE (APPLY (shiftUp 0 (shiftUp 0 f)) (VAR 0))
                              (VAR 0)
                              (APPLY (VAR 1) (SUC (VAR 0)))))))
    N0


#infSearch : CTerm → CTerm
#infSearch f =
  #APPLY
    (#FIX (#LAMBDA (#[0]LAMBDA (#[1]ITE (#[1]APPLY (#[1]shiftUp0 (#[0]shiftUp0 f)) (#[1]VAR0))
                                        (#[1]VAR0)
                                        (#[1]APPLY #[1]VAR1 (#[1]SUC #[1]VAR0))))))
    #N0


#infSearchP : CTerm → CTerm
#infSearchP f = #PAIR (#infSearch f) #AX


-- sanity check
⌜#infSearch⌝ : (f : CTerm) → ⌜ #infSearch f ⌝ ≡ infSearch ⌜ f ⌝
⌜#infSearch⌝ f = refl


∈#BOOL→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
            → equalInType i w #BOOL a b
            → □· w (λ w' _ → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' a b)
∈#BOOL→ u w a b b∈ = eqInType-⇛-BOOL u w a b (fst b∈) (snd b∈)


#⇛!sameℕ-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a b : CTerm}
                 → #⇛!sameℕ w1 a b
                 → #⇛!sameℕ w2 a b
#⇛!sameℕ-mon {w1} {w2} e {a} {b} (n , c₁ , c₂) = n , ∀𝕎-mon e c₁ , ∀𝕎-mon e c₂


∈#NAT!→BOOL→ : (i : ℕ) (w : 𝕎·) (f : CTerm)
                 → ∈Type i w #NAT!→BOOL f
                 → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → #⇛!sameℕ w' n₁ n₂
                                 → □· w' (λ w' e → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f n₁) (#APPLY f n₂)))
∈#NAT!→BOOL→ i w f f∈ w1 e1 n₁ n₂ n∈ =
  ∈#BOOL→
    i w1 (#APPLY f n₁) (#APPLY f n₂)
    (equalInType-FUN→ f∈ w1 e1 n₁ n₂ (→equalInType-NAT! i w1 n₁ n₂ (Mod.∀𝕎-□ M λ w2 e2 → #⇛!sameℕ-mon e2 {n₁} {n₂} n∈)))


mpSearch : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
           → ∈Type i w #NAT!→BOOL f
           → equalInType i w (#MP-right f) a₁ a₂
           → ∈Type i w (#MP-right2 f) (#infSearchP f)
mpSearch i w f a₁ a₂ f∈ a∈ =
  equalInType-local (Mod.∀𝕎-□Func M aw1 h1)
  where
    h1 : □· w (λ w' _ → inhType i w' (#MP-right2 f))
    h1 = equalInType-SQUASH→ a∈

    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2 f)
                         → ∈Type i w' (#MP-right2 f) (#infSearchP f))
    aw1 w1 e1 (t , t∈) =
      equalInType-local (Mod.∀𝕎-□Func M aw2 p∈) {--equalInType-SUM
        (λ w' _ → isTypeNAT!)
        (isType-MP-right-body i w1 f f (equalInType-mon f∈ w1 e1))
        {!!}--}
      where
        p∈ : □· w1 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t)
        p∈ = equalInType-SUM→ t∈

        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY (fromCTerm.⌞ CTermToCTerm0 ⌟ f) #[0]VAR)))) w' t t
                              → ∈Type i w' (#MP-right2 f) (#infSearchP f))
        aw2 w2 e2 (n₁ , n₂ , x₁ , x₂ , n∈ , c₁ , c₂ , x∈) =
          equalInType-local (Mod.∀𝕎-□Func M aw3 (equalInType-NAT!→ i w2 n₁ n₂ n∈))
          where
            y∈ : equalInType i w2 (#ASSERT₂ (#APPLY f n₁)) x₁ x₂
            y∈ = ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) x∈

            aw3 : ∀𝕎 w2 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                                  → ∈Type i w' (#MP-right2 f) (#infSearchP f))
            aw3 w3 e3 (n , d₁ , d₂) = {!!}
-- We'll have to compute with f using ∈#NAT!→BOOL→ potentially, but it has a □...
-- can we get rid of it for the 1st n's?

-- we have to also get y∈ down to a computation so that we can prove that the search terminate
-- because it at least terminate on n

\end{code}
