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


module not_mp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)


alwaysFreezable : Freeze W C K P G N → Set(L)
alwaysFreezable f = (c : Name) (w : 𝕎·) → Freeze.freezable f c w


-- Assuming that our choices are Bools
-- and that choices are always freezable (see where it is used below)
¬MP : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) → member w (#NEG #MP) #lamAX
¬MP bcb afb w = n , equalInType-NEG (isTypeMP w n) aw1
  where
    n : ℕ
    n = 1

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→BOOL f g
                             → equalInType n w' (sub0 f (#[0]FUN #[0]MP-left #[0]MP-right)) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT!→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→BOOL f g
                             → equalInType n w' (#FUN (#MP-left f) (#MP-right f)) (#APPLY F f) (#APPLY G g))
        aw3 w' e f g ex = ≡CTerm→equalInType (sub0-fun-mp f) (aw2 w' e f g ex)

        name : Name
        name = newChoice· w1

        w2 : 𝕎·
        w2 = startNewChoice Resℂ w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏ Resℂ w1

        oc1 : onlyℂ∈𝕎 (Res.def Resℂ) name w2
        oc1 n = getChoice-startNewChoice n Resℂ w1

        comp1 : compatible· name w2 Resℂ
        comp1 = startNewChoiceCompatible Resℂ w1

        fb1 : freezable· name w2
        fb1 = freezableStart· Resℂ w1

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→BOOL f
        eqf1 = →equalInType-CS-NAT!→BOOL eqf2

        h1 : equalInType n w2 (#FUN (#MP-left f) (#MP-right f)) (#APPLY F f) (#APPLY G f)
        h1 = aw3 w2 e2 f f eqf1

        h2 : ∀𝕎 w2 (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#MP-left f) a₁ a₂
                            → equalInType n w' (#MP-right f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
        h2 = equalInType-FUN→ h1

        h4 : ∀𝕎 w2 (λ w3 e3 → ¬ inhType n w3 (#PI-NEG-ASSERT₂ f))
        -- freezable might not be true here, but this is something that FCS will satisfy because freezable is always true...
        h4 w3 e3 inh = ¬∀𝕎¬equalInType-#Σchoice n w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (afb name w3) z
          where
            z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType n w4 (#Σchoice name ℂ₁·))
            z = equalInType-NEG→¬inh (snd (#PI-NEG-ASSERT₂→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh))

        h3 : inhType n w2 (#MP-left f)
        h3 = equalInType-NEG-inh {n} {w2} (→equalTypes-#PI-NEG-ASSERT₂ eqf1) h4

        h5 : □· w2 (λ w' _ → inhType n w' (#SUM-ASSERT₂ f))
        h5 = equalInType-SQUASH→ (h2 w2 (⊑-refl· _) (fst h3) (fst h3) (snd h3))

        -- We follow the choice
        w3 : 𝕎·
        w3 = fst (ChoiceBar.followChoice CB name h5 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (ChoiceBar.followChoice CB name h5 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
        oc2 = fst (snd (snd (ChoiceBar.followChoice CB name h5 oc1 comp1 fb1)))

        comp2 : compatible· name w3 Resℂ
        comp2 = fst (snd (snd (snd (ChoiceBar.followChoice CB name h5 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB name h5 oc1 comp1 fb1)))))

        h6 : inhType n w3 (#SUM-ASSERT₂ f)
        h6 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB name h5 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice name ℂ₁·)
        h7 = #SUM-ASSERT₂→#Σchoice bcb comp2 (0 , sat-ℂ₁ 0) h6

        h8 : ¬ inhType n w3 (#Σchoice name ℂ₁·)
        h8 = ¬equalInType-#Σchoice n w3 Resℂ name isValueℂ₀· isValueℂ₁· ¬∼ℂ₀₁· oc2 comp2 fb2


-- This is similar to ¬MP but proved here for #MP₂, which is stated using ¬¬∃, instead of #MP, which is stated using ¬∀¬
¬MP₂ : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) → member w (#NEG #MP₂) #lamAX
¬MP₂ bcb afb w =
  n , →∈Type-NEG n w #MP #MP₂ #lamAX #lamAX (isTypeMP₂ w n) aw1 (snd (¬MP bcb afb w))
  where
    n : ℕ
    n = 1

    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' #NAT!→BOOL f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp f₁))
        (sym (sub0-fun-mp f₂))
        (eqTypesFUN← (→equalTypes-#MP-left f∈) (→equalTypes-#MP-right f∈))

    p3 : ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type n w' #NAT!→BOOL a
                       → equalInType n w' (sub0 a (#[0]FUN #[0]MP-left3 #[0]MP-right)) b₁ b₂
                       → equalInType n w' (sub0 a (#[0]FUN #[0]MP-left #[0]MP-right)) b₁ b₂)
    p3 w1 e1 a b₁ b₂ a∈ b∈ =
      →≡equalInType
        (sym (sub0-fun-mp a))
        (→∈Type-FUN
           n w1 (#MP-left3 a) (#MP-left a) (#MP-right a) (#MP-right a)
           b₁ b₂ (→equalTypes-#MP-left a∈) (→equalTypes-#MP-right a∈)
           (λ w2 e2 x y h → #MP-left2→#MP-left3 n w2 a x y (equalInType-mon a∈ w2 e2) (#MP-left→#MP-left2 n w2 a x y (equalInType-mon a∈ w2 e2) h))
           (λ w2 e2 a b h → h) (→≡equalInType (sub0-fun-mp₂ a) b∈))

    aw1 : ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' #MP₂ u₁ u₂ → equalInType n w' #MP u₁ u₂)
    aw1 w1 e1 u₁ u₂ u∈ =
      →∈Type-PI
        n w1 #NAT!→BOOL #NAT!→BOOL
        (#[0]FUN #[0]MP-left3 #[0]MP-right)
        (#[0]FUN #[0]MP-left #[0]MP-right)
        u₁ u₂ (isType-#NAT!→BOOL w1 n) (∀𝕎-mon e1 p2) (λ w1 e1 a b h → h)
        (∀𝕎-mon e1 p3) u∈


-- This is similar to ¬MP₂ but proved here for an non-truncated version of #MP₂
¬MP₃ : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) → member w (#NEG #MP₃) #lamAX
¬MP₃ bcb afb w =
  n , →∈Type-NEG n w #MP₂ #MP₃ #lamAX #lamAX (isTypeMP₃ w n) aw1 (snd (¬MP₂ bcb afb w))
  where
    n : ℕ
    n = 1

    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' #NAT!→BOOL f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left3 #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left3 #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp₂ f₁))
        (sym (sub0-fun-mp₂ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left3 f∈) (→equalTypes-#MP-right f∈))

    p3 : ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type n w' #NAT!→BOOL a
                       → equalInType n w' (sub0 a (#[0]FUN #[0]MP-left2 #[0]MP-right2)) b₁ b₂
                       → equalInType n w' (sub0 a (#[0]FUN #[0]MP-left3 #[0]MP-right)) b₁ b₂)
    p3 w1 e1 a b₁ b₂ a∈ b∈ =
      →≡equalInType
        (sym (sub0-fun-mp₂ a))
        (→∈Type-FUN
          n w1 (#MP-left2 a) (#MP-left3 a) (#MP-right2 a) (#MP-right a) b₁ b₂
          (→equalTypes-#MP-left3 a∈) (→equalTypes-#MP-right a∈)
          (λ w2 e2 x y h → #MP-left3→#MP-left2 n w2 a x y (equalInType-mon a∈ w2 e2) h)
          (λ w2 e2 x y h → ∈#MP-right2→∈MP-right n w2 a x y x y (equalInType-mon a∈ w2 e2) h)
          (→≡equalInType (sub0-fun-mp₃ a) b∈))

    aw1 : ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' #MP₃ u₁ u₂ → equalInType n w' #MP₂ u₁ u₂)
    aw1 w1 e1 u₁ u₂ u∈ = →∈Type-PI
        n w1 #NAT!→BOOL #NAT!→BOOL
        (#[0]FUN #[0]MP-left2 #[0]MP-right2)
        (#[0]FUN #[0]MP-left3 #[0]MP-right)
        u₁ u₂ (isType-#NAT!→BOOL w1 n) (∀𝕎-mon e1 p2) (λ w1 e1 a b h → h)
        (∀𝕎-mon e1 p3) u∈

\end{code}[hide]
