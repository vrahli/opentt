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


module mp_props {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



-- π (F : ℕ → 𝔹). ¬(Π (n : ℕ). ¬(F n ≡ true)) → ||Σ (n : ℕ). F n ≡ true||
MP : Term
MP = PI NAT!→BOOL (FUN (NEG (PI NAT! (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))
                        (SQUASH (SUM NAT! (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))


#MP : CTerm
#MP = ct MP c
  where
    c : # MP
    c = refl


-- Similar to #[0]MP-right (without the squash): Σ(n:ℕ).f(n)=true
#[0]MP-right2 : CTerm0
#[0]MP-right2 = #[0]SUM #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right : CTerm0
#[0]MP-right = #[0]SQUASH #[0]MP-right2


-- ¬Π(n : ℕ).¬(f(n)=true)
#[0]MP-left : CTerm0
#[0]MP-left = #[0]NEG (#[0]PI #[0]NAT! (#[1]NEG (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))))


-- Similar to #[0]MP-left: ¬¬Σ(n:ℕ).f(n)=true
#[0]MP-left2 : CTerm0
#[0]MP-left2 = #[0]NEG (#[0]NEG #[0]MP-right2)


-- Similar to #[0]MP-left2 (with a squash): ¬¬↓Σ(n:ℕ).f(n)=true
#[0]MP-left3 : CTerm0
#[0]MP-left3 = #[0]NEG (#[0]NEG #[0]MP-right)


-- Σ(n:ℕ).f(n)=true
#MP-right2 : CTerm → CTerm
#MP-right2 f = #SUM-ASSERT₂ f


-- ↓Σ(n:ℕ).f(n)=true
#MP-right : CTerm → CTerm
#MP-right f = #SQUASH (#MP-right2 f)


-- ¬Π(n : ℕ).¬(f(n)=true)
#MP-left : CTerm → CTerm
#MP-left f = #NEG (#PI-NEG-ASSERT₂ f)


-- ¬¬Σ(n:ℕ).f(n)=true
#MP-left2 : CTerm → CTerm
#MP-left2 f = #NEG (#NEG (#MP-right2 f))


-- ¬¬↓Σ(n:ℕ).f(n)=true
#MP-left3 : CTerm → CTerm
#MP-left3 f = #NEG (#NEG (#MP-right f))


#MP-PI : CTerm
#MP-PI = #PI #NAT!→BOOL (#[0]FUN #[0]MP-left #[0]MP-right)


#MP≡#PI : #MP ≡ #MP-PI
#MP≡#PI = CTerm≡ refl


-- Another version of MP using ¬¬Σ instead of ¬∀
#MP₂ : CTerm
#MP₂ = #PI #NAT!→BOOL (#[0]FUN #[0]MP-left3 #[0]MP-right)


sub0-fun-mp : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left #[0]MP-right)
                             ≡ #FUN (#MP-left a) (#MP-right a)
sub0-fun-mp a =
  ≡sub0-#[0]FUN
    a #[0]MP-left #[0]MP-right (#MP-left a) (#MP-right a)
    (CTerm≡ (≡NEG (≡PI refl (≡NEG (≡ASSERT₂ (→≡APPLY e refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


sub0-fun-mp₂ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left3 #[0]MP-right)
                             ≡ #FUN (#MP-left3 a) (#MP-right a)
sub0-fun-mp₂ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left3 #[0]MP-right (#MP-left3 a) (#MP-right a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY e1 refl) refl refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl

    e1 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


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


∀𝕎∃𝕎-func : {w : 𝕎·} {f g : wPred w}
              → ∀𝕎 w (λ w1 e1 → f w1 e1 → g w1 e1)
              → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (↑wPred f e1))
              → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (↑wPred g e1))
∀𝕎∃𝕎-func {w} {f} {g} h q w1 e1 =
  fst q' , fst (snd q') , h (fst q') (⊑-trans· e1 (fst (snd q'))) (snd (snd q'))
  where
    q' : ∃𝕎 w1 (↑wPred f e1)
    q' = q w1 e1


→equalTypes-#MP-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL a₁ a₂
                        → equalTypes n w (#MP-left a₁) (#MP-left a₂)
→equalTypes-#MP-left {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (→equalTypes-#PI-NEG-ASSERT₂ eqt)


→equalTypes-#MP-left3 : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL a₁ a₂
                        → equalTypes n w (#MP-left3 a₁) (#MP-left3 a₂)
→equalTypes-#MP-left3 {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ eqt)))


isType-MP-right-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                       → equalInType i w #NAT!→BOOL f₁ f₂
                       → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                                        → equalTypes i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                           (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-right-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERT₂-APPLY a₁ f₁))
    (sym (sub0-ASSERT₂-APPLY a₂ f₂))
    (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ f∈ w1 e1 a₁ a₂ a∈))


→equalTypes-#MP-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT!→BOOL a₁ a₂
                          → equalTypes n w (#MP-right a₁) (#MP-right a₂)
→equalTypes-#MP-right {n} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (eqTypesSUM← (λ w' _ → isTypeNAT!) (isType-MP-right-body n w a₁ a₂ eqt))


isTypeMP-PI : (w : 𝕎·) (n : ℕ) → isType n w #MP-PI
isTypeMP-PI w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right}
    {#NAT!→BOOL} {#[0]FUN #[0]MP-left #[0]MP-right}
    (λ w' e → isType-#NAT!→BOOL w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp a₁ | sub0-fun-mp a₂ =
      eqTypesFUN← (→equalTypes-#MP-left eqb) (→equalTypes-#MP-right eqb)



isTypeMP₂ : (w : 𝕎·) (n : ℕ) → isType n w #MP₂
isTypeMP₂ w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL} {#[0]FUN #[0]MP-left3 #[0]MP-right}
    {#NAT!→BOOL} {#[0]FUN #[0]MP-left3 #[0]MP-right}
    (λ w' e → isType-#NAT!→BOOL w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left3 #[0]MP-right))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left3 #[0]MP-right)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₂ a₁ | sub0-fun-mp₂ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left3 eqb) (→equalTypes-#MP-right eqb)



isTypeMP : (w : 𝕎·) (n : ℕ) → isType n w #MP
isTypeMP w n rewrite #MP≡#PI = isTypeMP-PI w n


isTypeNegMP : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #MP)
isTypeNegMP w n = eqTypesNEG← (isTypeMP w n)


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


-- We prove that the result in equalInType-#MP-left→ is an equivalence
→equalInType-#MP-left : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                         → ∈Type i w #NAT!→BOOL f
                         → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                                           → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                                           → ⊥)
                                          → ⊥)
                        → equalInType i w (#MP-left f) a₁ a₂
→equalInType-#MP-left i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (→equalTypes-#PI-NEG-ASSERT₂ f∈)
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#PI-NEG-ASSERT₂ f) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂ → inhType i w' (#ASSERT₂ (#APPLY f n₁)) → ⊥)
        aw2 w2 e2 n₁ n₂ n∈ (t , inh) = h1 w2 (⊑-refl· w2) t t inh
          where
            h1 : ∀𝕎 w2 (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' (#ASSERT₂ (#APPLY f n₁)) a₁ a₂)
            h1 = equalInType-NEG→ (≡CTerm→equalInType (sub0-NEG-ASSERT₂-APPLY n₁ f) (snd (snd (equalInType-PI→ g∈)) w2 e2 n₁ n₂ n∈))



-- This is a simple unfolding of what it means to be a member of (#MP-left2 f)
equalInType-#MP-left2→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL f
                          → equalInType i w (#MP-left2 f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
equalInType-#MP-left2→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SUM-ASSERT₂ f) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw h3))
      where
        aw : ∀𝕎 w2 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂ → Lift (lsuc L) ⊥)
        aw w3 e3 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
          lift (h w3 (⊑-trans· e2 e3) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-refl q∈)))

        h3 : □· w2 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂)
        h3 = equalInType-SUM→ p∈

    h1 : ∈Type i w1 (#NEG (#SUM-ASSERT₂ f)) t
    h1 = equalInType-NEG
           (→equalTypes-#SUM-ASSERT₂ (equalInType-mon f∈ w1 e1))
           h2


→equalInType-#MP-left2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-left2 f) a₁ a₂
→equalInType-#MP-left2 i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (→equalTypes-#SUM-ASSERT₂ f∈))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SUM-ASSERT₂ f)) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                   × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 (#PAIR n₁ t) (#PAIR n₂ t) p∈
          where
            aw3 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₂ t))
            aw3 w3 e3 =
              n₁ , n₂ , t , t ,
              equalInType-mon n∈ w3 e3 ,
              #compAllRefl (#PAIR n₁ t) w3 ,
              #compAllRefl (#PAIR n₂ t) w3 ,
              ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f)) (equalInType-mon inh w3 e3)

            p∈ : equalInType i w2 (#SUM-ASSERT₂ f) (#PAIR n₁ t) (#PAIR n₂ t)
            p∈ = equalInType-SUM
                    (λ w' _ → isTypeNAT!)
                    (isType-MP-right-body i w2 f f (equalInType-mon f∈ w2 (⊑-trans· e1 e2)))
                    (Mod.∀𝕎-□ M aw3)


-- This is a simple unfolding of what it means to be a member of (#MP-left3 f)
equalInType-#MP-left3→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL f
                          → equalInType i w (#MP-left3 f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
equalInType-#MP-left3→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SQUASH (#SUM-ASSERT₂ f)) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 h3))
      where
        aw1 : ∀𝕎 w2 (λ w' e' → inhType i w' (#SUM-ASSERT₂ f) → Lift (lsuc L) ⊥)
        aw1 w3 e3 (u , u∈) = Mod.□-const M (Mod.∀𝕎-□Func M aw2 h4)
          where
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM→ u∈

        h3 : □· w2 (λ w' _ → inhType i w' (#SUM-ASSERT₂ f))
        h3 = equalInType-SQUASH→ p∈

    h1 : ∈Type i w1 (#NEG (#SQUASH (#SUM-ASSERT₂ f))) t
    h1 = equalInType-NEG
           (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ (equalInType-mon f∈ w1 e1)))
           h2


→equalInType-#MP-left3 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-left3 f) a₁ a₂
→equalInType-#MP-left3 i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SQUASH (#SUM-ASSERT₂ f))) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                   × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType i w' (#SUM-ASSERT₂ f))
            i∈ w3 e3 =
              #PAIR n₁ t ,
              equalInType-SUM
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  #compAllRefl (#PAIR n₁ t) w4 ,
                  #compAllRefl (#PAIR n₁ t) w4 ,
                  ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f)) (equalInType-mon inh w4 (⊑-trans· e3 e4))

            s∈ : equalInType i w2 (#SQUASH (#SUM-ASSERT₂ f)) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)


#MP-left2→#MP-left : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                      → ∈Type i w #NAT!→BOOL f
                      → equalInType i w (#MP-left2 f) a₁ a₂
                      → equalInType i w (#MP-left f) a₁ a₂
#MP-left2→#MP-left i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left i w f a₁ a₂ f∈ aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                          → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                          → ⊥)
                        → ⊥)
    aw1 w1 e1 h = equalInType-#MP-left2→ i w f a₁ a₂ f∈ a∈ w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                    × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , inh) = h w2 e2 n₁ n₂ n∈ inh



#MP-left→#MP-left2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                      → ∈Type i w #NAT!→BOOL f
                      → equalInType i w (#MP-left f) a₁ a₂
                      → equalInType i w (#MP-left2 f) a₁ a₂
#MP-left→#MP-left2 i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left2 i w f a₁ a₂ f∈ aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                    × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥) → ⊥)
    aw1 w1 e1 h = equalInType-#MP-left→ i w f a₁ a₂ f∈ a∈ w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                          → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                          → ⊥)
        aw2 w2 e2 n₁ n₂ n∈ inh = h w2 e2 (n₁ , n₂ , n∈ , inh)


#MP-left2→#MP-left3 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                       → ∈Type i w #NAT!→BOOL f
                       → equalInType i w (#MP-left2 f) a₁ a₂
                       → equalInType i w (#MP-left3 f) a₁ a₂
#MP-left2→#MP-left3 i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left3 i w f a₁ a₂ f∈ (equalInType-#MP-left2→ i w f a₁ a₂ f∈ a∈)


#MP-left3→#MP-left2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                       → ∈Type i w #NAT!→BOOL f
                       → equalInType i w (#MP-left3 f) a₁ a₂
                       → equalInType i w (#MP-left2 f) a₁ a₂
#MP-left3→#MP-left2 i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left2 i w f a₁ a₂ f∈ (equalInType-#MP-left3→ i w f a₁ a₂ f∈ a∈)


→∈Type-NEG : (i : ℕ) (w : 𝕎·) (A B : CTerm) (t₁ t₂ : CTerm)
               → isType i w B
               → ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType i w' B u₁ u₂ → equalInType i w' A u₁ u₂)
               → equalInType i w (#NEG A) t₁ t₂
               → equalInType i w (#NEG B) t₁ t₂
→∈Type-NEG i w A B t₁ t₂ ist h a∈ =
  equalInType-NEG ist aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' B a₁ a₂)
    aw1 w1 e1 a₁ a₂ q = equalInType-NEG→ a∈ w1 e1 a₁ a₂ (h w1 e1 a₁ a₂ q)


→∈Type-PI : (i : ℕ) (w : 𝕎·) (A B : CTerm) (C D : CTerm0) (t₁ t₂ : CTerm)
               → isType i w B
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' B a₁ a₂ → equalTypes i w' (sub0 a₁ D) (sub0 a₂ D))
               → ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType i w' B u₁ u₂ → equalInType i w' A u₁ u₂)
               → ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type i w' B a → equalInType i w' (sub0 a C) b₁ b₂ → equalInType i w' (sub0 a D) b₁ b₂)
               → equalInType i w (#PI A C) t₁ t₂
               → equalInType i w (#PI B D) t₁ t₂
→∈Type-PI i w A B C D t₁ t₂ istb istd ha hb a∈ =
  equalInType-PI (λ w' e' → eqTypes-mon (uni i) istb w' e') istd aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' B a₁ a₂
                        → equalInType i w' (sub0 a₁ D) (#APPLY t₁ a₁) (#APPLY t₂ a₂))
    aw1 w1 e1 a₁ a₂ q =
      hb w1 e1 a₁ (#APPLY t₁ a₁) (#APPLY t₂ a₂) (equalInType-refl q)
         (snd (snd (equalInType-PI→ a∈)) w1 e1 a₁ a₂ (ha w1 e1 a₁ a₂ q))


→∈Type-FUN : (i : ℕ) (w : 𝕎·) (A B C D : CTerm) (t₁ t₂ : CTerm)
               → isType i w B
               → isType i w D
               → ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType i w' B u₁ u₂ → equalInType i w' A u₁ u₂)
               → ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' C b₁ b₂ → equalInType i w' D b₁ b₂)
               → equalInType i w (#FUN A C) t₁ t₂
               → equalInType i w (#FUN B D) t₁ t₂
→∈Type-FUN i w A B C D t₁ t₂ istb istd ha hb a∈ =
  equalInType-FUN istb istd aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' B a₁ a₂
                        → equalInType i w' D (#APPLY t₁ a₁) (#APPLY t₂ a₂))
    aw1 w1 e1 a₁ a₂ q =
      hb w1 e1 (#APPLY t₁ a₁) (#APPLY t₂ a₂)
         (equalInType-FUN→ a∈ w1 e1 a₁ a₂ (ha w1 e1 a₁ a₂ q))

\end{code}[hide]
