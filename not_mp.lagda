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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
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
open import progress
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import mod


module not_mp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
              (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C K G) (N : NewChoice {L} W C K G)
              (F : Freeze {L} W C K P G N)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
              (CB : ChoiceBar W M C K P G X N F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)



MP : Term
MP = PI NAT→BOOL (FUN (NEG (PI NAT (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))
                       (SQUASH (SUM NAT (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))


#MP : CTerm
#MP = ct MP c
  where
    c : # MP
    c = refl



#[0]MP-left : CTerm0
#[0]MP-left = #[0]NEG (#[0]PI #[0]NAT (#[1]NEG (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))))


#[0]MP-right : CTerm0
#[0]MP-right = #[0]SQUASH (#[0]SUM #[0]NAT (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0)))


#MP-left : CTerm → CTerm
#MP-left f = #NEG (#PI-NEG-ASSERT₂ f)


#MP-right : CTerm → CTerm
#MP-right f = #SQUASH (#SUM-ASSERT₂ f)


#MP-PI : CTerm
#MP-PI = #PI #NAT→BOOL (#[0]FUN #[0]MP-left #[0]MP-right)


#MP≡#PI : #MP ≡ #MP-PI
#MP≡#PI = CTerm≡ refl



sub0-fun-mp : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left #[0]MP-right)
                             ≡ #FUN (#MP-left a) (#MP-right a)
sub0-fun-mp a =
  ≡sub0-#[0]FUN
    a #[0]MP-left #[0]MP-right (#MP-left a) (#MP-right a)
    (CTerm≡ (≡NEG (≡PI refl (≡NEG (≡ASSERT₂ (→≡APPLY e refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl





→equalTypes-#MP-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT→BOOL a₁ a₂
                        → equalTypes n w (#MP-left a₁) (#MP-left a₂)
→equalTypes-#MP-left {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (→equalTypes-#PI-NEG-ASSERT₂ eqt)


→equalTypes-#MP-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT→BOOL a₁ a₂
                          → equalTypes n w (#MP-right a₁) (#MP-right a₂)
→equalTypes-#MP-right {n} {w} {a₁} {a₂} eqt = eqTypesSQUASH← (eqTypesSUM← (λ w' _ → eqTypesNAT) aw1)
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₂-APPLY a a₁ | sub0-ASSERT₂-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₂ (#APPLY a₁ a)) (#ASSERT₂ (#APPLY a₂ b))
        aw2 = equalInType-BOOL→equalTypes-ASSERT₂ eqb



isTypeMP-PI : (w : 𝕎·) (n : ℕ) → isType n w #MP-PI
isTypeMP-PI w n =
  eqTypesPI←
    {w} {n}
    {#NAT→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right}
    {#NAT→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right}
    (λ w' e → isType-#NAT→BOOL w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT→BOOL a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp a₁ | sub0-fun-mp a₂ =
      eqTypesFUN← (→equalTypes-#MP-left eqb) (→equalTypes-#MP-right eqb)



isTypeMP : (w : 𝕎·) (n : ℕ) → isType n w #MP
isTypeMP w n rewrite #MP≡#PI = isTypeMP-PI w n


isTypeNegMP : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #MP)
isTypeNegMP w n = eqTypesNEG← (isTypeMP w n)


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
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT→BOOL f g
                             → equalInType n w' (sub0 f (#[0]FUN #[0]MP-left #[0]MP-right)) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT→BOOL f g
                             → equalInType n w' (#FUN (#MP-left f) (#MP-right f)) (#APPLY F f) (#APPLY G g))
        aw3 w' e f g ex = ≡CTerm→equalInType (sub0-fun-mp f) (aw2 w' e f g ex)

        name : Name
        name = newChoice· w1

        w2 : 𝕎·
        w2 = startNewChoice Resℂ w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏· Resℂ w1

        oc1 : onlyℂ∈𝕎 (Res.def Resℂ) name w2
        oc1 n = getChoice-startNewChoice· n Resℂ w1

        comp1 : compatible· name w2 Resℂ
        comp1 = startChoiceCompatible· Resℂ w1

        fb1 : freezable· name w2
        fb1 = freezableStart· Resℂ w1

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT n w' m))

        eqf1 : ∈Type n w2 #NAT→BOOL f
        eqf1 = →equalInType-CS-NAT→BOOL eqf2

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

\end{code}[hide]
