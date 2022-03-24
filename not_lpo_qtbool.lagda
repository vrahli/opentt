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
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import mod


module not_lpo_qtbool {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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


{-- This version is similar to the one presented in not_lpo, but relies on QTBOOL instead of BOOL,
 -- which allows us to use references to prove it and not just FCS.
 --}

LPO : Term
LPO = PI NAT!→QTBOOL! (SQUASH (UNION (SUM NAT! (ASSERT₃ (APPLY (VAR 1) (VAR 0))))
                                     (PI NAT! (NEG (ASSERT₃ (APPLY (VAR 1) (VAR 0)))))))


#LPO : CTerm
#LPO = ct LPO c
  where
    c : # LPO
    c = refl



#[0]LPO-left : CTerm0
#[0]LPO-left = #[0]SUM #[0]NAT! (#[1]ASSERT₃ (#[1]APPLY #[1]VAR1 #[1]VAR0))


#[0]LPO-right : CTerm0
#[0]LPO-right = #[0]PI #[0]NAT! (#[1]NEG (#[1]ASSERT₃ (#[1]APPLY #[1]VAR1 #[1]VAR0)))


#LPO-left : CTerm → CTerm
#LPO-left = #SUM-ASSERT₃


#LPO-right : CTerm → CTerm
#LPO-right = #PI-NEG-ASSERT₃


#LPO-PI : CTerm
#LPO-PI = #PI #NAT!→QTBOOL! (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))


#LPO≡#PI : #LPO ≡ #LPO-PI
#LPO≡#PI = CTerm≡ refl



sub0-squash-union-LPO : (a : CTerm) → sub0 a (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))
                                       ≡ #SQUASH (#UNION (#LPO-left a) (#LPO-right a))
sub0-squash-union-LPO a =
  ≡sub0-#[0]SQUASH a (#[0]UNION #[0]LPO-left #[0]LPO-right) (#UNION (#LPO-left a) (#LPO-right a))
                   (CTerm≡ (≡UNION (≡SUM refl (≡ASSERT₃ (→≡APPLY e refl))) (≡PI refl (≡NEG (≡ASSERT₃ (→≡APPLY e refl))))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl



isTypeLPO-PI : (w : 𝕎·) (n : ℕ) → isType n w #LPO-PI
isTypeLPO-PI w n =
  eqTypesPI← {w} {n}
              {#NAT!→QTBOOL!} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)}
              {#NAT!→QTBOOL!} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)}
              (λ w' e → isType-#NAT!→QTBOOL! w' n)
              aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→QTBOOL! a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)))
                                         (sub0 a₂ (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))))
    aw w' e a₁ a₂ eqb rewrite sub0-squash-union-LPO a₁ | sub0-squash-union-LPO a₂ = eqt
      where
        eqt1 : equalTypes n w' (#LPO-left a₁) (#LPO-left a₂)
        eqt1 = →equalTypes-#SUM-ASSERT₃ eqb

        eqt2 : equalTypes n w' (#LPO-right a₁) (#LPO-right a₂)
        eqt2 = →equalTypes-#PI-NEG-ASSERT₃ eqb

        eqt : equalTypes n w' (#SQUASH (#UNION (#LPO-left a₁) (#LPO-right a₁))) (#SQUASH (#UNION (#LPO-left a₂) (#LPO-right a₂)))
        eqt = eqTypesSQUASH← (eqTypesUNION← eqt1 eqt2)



isTypeLPO : (w : 𝕎·) (n : ℕ) → isType n w #LPO
isTypeLPO w n rewrite #LPO≡#PI = isTypeLPO-PI w n


isTypeNegLPO : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #LPO)
isTypeNegLPO w n = eqTypesNEG← (isTypeLPO w n)



-- MOVE to props3
→equalInType-CS-NAT!→QTBOOL! : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #QTBOOL! (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT!→QTBOOL! (#CS a) (#CS b)
→equalInType-CS-NAT!→QTBOOL! {n} {w} {a} {b} i rewrite #NAT!→QTBOOL!≡ = →equalInType-CS-NAT!→T (eqTypesQTBOOL! {w} {n}) i



-- Assuming that our choices are QTBools
¬LPO : QTBoolℂ CB → (w : 𝕎·) → member w (#NEG #LPO) #lamAX
¬LPO bcb w = n , equalInType-NEG (isTypeLPO w n) aw1
  where
    n : ℕ
    n = 1

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #LPO a₁ a₂)
    aw1 w1 e1 F G ea =
      h (fun-equalInType-SQUASH-UNION (equalInType-#Σchoice w2 name ℂ₁· comp1 (0 , sat-ℂ₁ 0))
                                      (eqTypesNEG← (equalInType-#Σchoice w2 name ℂ₁· comp1 (0 , sat-ℂ₁ 0)))
                                      imp1
                                      imp2
                                      h1)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→QTBOOL! f g
                             → equalInType n w' (sub0 f (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT!→QTBOOL!} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→QTBOOL! f g
                             → equalInType n w' (#SQUASH (#UNION (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G g))
        aw3 w' e f g ex = ≡CTerm→equalInType (sub0-squash-union-LPO f) (aw2 w' e f g ex)

        name : Name
        name = newChoice· w1

        w2 : 𝕎·
        w2 = startNewChoice Resℂ w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏ Resℂ w1

        comp1 : compatible· name w2 Resℂ
        comp1 = startNewChoiceCompatible Resℂ w1

        h : ¬ equalInType n w2 (sq-dec (#Σchoice name ℂ₁·)) #AX #AX
        h = ¬-dec-Σchoice w1 n

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #QTBOOL! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→QTBOOL! f
        eqf1 = →equalInType-CS-NAT!→QTBOOL! eqf2

        h1 : equalInType n w2 (#SQUASH (#UNION (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G f)
        h1 = aw3 w2 e2 f f eqf1

        imp1 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-left f) → inhType n w' (#Σchoice name ℂ₁·))
        imp1 w3 e3 inh = #SUM-ASSERT₃→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh

        imp2 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-right f) → inhType n w' (#NEG (#Σchoice name ℂ₁·)))
        imp2 w3 e3 inh = #PI-NEG-ASSERT₃→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh

\end{code}[hide]
