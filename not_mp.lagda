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


module not_mp {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (P : Progress {L} W C M)
              (G : GetChoice {L} W C M) (X : ChoiceExt {L} C) (N : NewChoice {L} W C M G)
              (F : Freeze {L} W C M P G N)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
              (CB : ChoiceBar W C M P G X N F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import newChoiceDef(W)(C)(M)(G)(N)
open import choiceExtDef(W)(C)(M)(G)(X)
open import freezeDef(W)(C)(M)(P)(G)(N)(F)
open import computation(W)(C)(M)(G)
open import bar(W)
open import barI(W)(C)(M)(P)
open import theory(W)(C)(M)(P)(G)(E)
open import props0(W)(C)(M)(P)(G)(E)
open import ind2(W)(C)(M)(P)(G)(E)

open import props1(W)(C)(M)(P)(G)(E)
open import props2(W)(C)(M)(P)(G)(E)
open import props3(W)(C)(M)(P)(G)(E)
open import lem_props(W)(C)(M)(P)(G)(X)(E)

open import choiceBarDef(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
open import not_lem(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
open import typeC(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
open import boolC(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)



loweVars-suc : (l : List Var) → lowerVars (Data.List.map (λ x → suc x) l) ≡ l
loweVars-suc [] = refl
loweVars-suc (x ∷ l) rewrite loweVars-suc l = refl


fvars-FUN0 : (a b : Term) → fvars (FUN a b) ≡ fvars a ++ fvars b
fvars-FUN0 a b rewrite fvars-shiftUp≡ 0 b | lowerVars-map-sucIf≤-suc 0 (fvars b) | loweVars-suc (fvars b) = refl



-- MOVE to terms.lagda
#[0]FUN : CTerm0 → CTerm0 → CTerm0
#[0]FUN a b = ct0 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                           (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))



sub0-#[0]FUN : (a : CTerm) (t u : CTerm0)
               → sub0 a (#[0]FUN t u) ≡ #FUN (sub0 a t) (sub0 a u)
sub0-#[0]FUN a t u = CTerm≡ (≡PI refl e)
  where
    e : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) (shiftUp 0 ⌜ u ⌝)) ≡ shiftUp 0 ⌜ sub0 a u ⌝
    e rewrite #shiftUp 0 a
            | #shiftDown 0 (ct (subv 0 ⌜ a ⌝ ⌜ u ⌝) (#subv-CTerm a u))
            | #shiftUp 0 (ct (subv 0 ⌜ a ⌝ ⌜ u ⌝) (#subv-CTerm a u))
            | #shiftUp 0 a
            | shiftDown1-subv1-shiftUp0 0 ⌜ a ⌝ ⌜ u ⌝ (CTerm.closed a) = refl



≡sub0-#[0]FUN : (a : CTerm) (b c : CTerm0) (u v : CTerm)
                 → sub0 a b ≡ u
                 → sub0 a c ≡ v
                 → sub0 a (#[0]FUN b c) ≡ #FUN u v
≡sub0-#[0]FUN a b c u v e f rewrite sym e | sym f = sub0-#[0]FUN a b c


≡FUN : {a b c d : Term} → a ≡ b → c ≡ d → FUN a c ≡ FUN b d
≡FUN {a} {b} {c} {d} e f rewrite e | f = refl

-----



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
#MP-left f = #NEG (#PI #NAT (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))


#MP-right : CTerm → CTerm
#MP-right f = #SQUASH (#SUM #NAT (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))


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
  eqTypesNEG← (eqTypesPI← (λ w' _ → eqTypesNAT) aw1)
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT a b)
                       → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                          (sub0 b (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR)))))
    aw1 w' e a b ea rewrite sub0-NEG-ASSERT-APPLY a a₁ | sub0-NEG-ASSERT-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#NEG (#ASSERT₂ (#APPLY a₁ a))) (#NEG (#ASSERT₂ (#APPLY a₂ b)))
        aw2 = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT₂ eqb)


→equalTypes-#MP-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT→BOOL a₁ a₂
                          → equalTypes n w (#MP-right a₁) (#MP-right a₂)
→equalTypes-#MP-right {n} {w} {a₁} {a₂} eqt = eqTypesSQUASH← (eqTypesSUM← (λ w' _ → eqTypesNAT) aw1)
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT-APPLY a a₁ | sub0-ASSERT-APPLY b a₂ = aw2
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



-- TODO: We need to extract the 2 branches of ¬-dec-Σchoice in not_lem to use them here
--
-- Assuming that our choices are Bools
¬MP : Boolℂ CB → (w : 𝕎·) → member w (#NEG #MP) #lamAX
¬MP bcb w = n , equalInType-NEG (λ w1 e1 → isTypeMP w1 n) aw1
  where
    n : ℕ
    n = 1

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP a₁ a₂)
    aw1 w1 e1 F G ea = {!!}
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

        comp1 : compatible· name w2 Resℂ
        comp1 = startChoiceCompatible· Resℂ w1

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT n w' m))

        eqf1 : ∈Type n w2 #NAT→BOOL f
        eqf1 = →equalInType-CS-NAT→BOOL eqf2

        h1 : equalInType n w2 (#FUN (#MP-left f) (#MP-right f)) (#APPLY F f) (#APPLY G f)
        h1 = aw3 w2 e2 f f eqf1
\end{code}[hide]
