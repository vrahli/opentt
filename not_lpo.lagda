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


module not_lpo {L : Level} (W : PossibleWorlds {L})
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



LPO : Term
LPO = PI NAT→BOOL (SQUASH (UNION (SUM NAT (ASSERT₂ (APPLY (VAR 1) (VAR 0))))
                                  (PI NAT (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0)))))))


#LPO : CTerm
#LPO = ct LPO c
  where
    c : # LPO
    c = refl



#[0]LPO-left : CTerm0
#[0]LPO-left = #[0]SUM #[0]NAT (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))


#[0]LPO-right : CTerm0
#[0]LPO-right = #[0]PI #[0]NAT (#[1]NEG (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0)))


#LPO-left : CTerm → CTerm
#LPO-left f = #SUM #NAT (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#LPO-right : CTerm → CTerm
#LPO-right f = #PI #NAT (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))


#LPO-PI : CTerm
#LPO-PI = #PI #NAT→BOOL (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))


#LPO≡#PI : #LPO ≡ #LPO-PI
#LPO≡#PI = CTerm≡ refl



sub0-squash-union-LPO : (a : CTerm) → sub0 a (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))
                                       ≡ #SQUASH (#UNION (#LPO-left a) (#LPO-right a))
sub0-squash-union-LPO a =
  ≡sub0-#[0]SQUASH a (#[0]UNION #[0]LPO-left #[0]LPO-right) (#UNION (#LPO-left a) (#LPO-right a))
                   (CTerm≡ (≡UNION (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl))) (≡PI refl (≡NEG (≡ASSERT₂ (→≡APPLY e refl))))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl




→equalTypes-#LPO-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                         → equalInType n w #NAT→BOOL a₁ a₂
                         → equalTypes n w (#LPO-left a₁) (#LPO-left a₂)
→equalTypes-#LPO-left {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → eqTypesNAT) aw1
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


→equalTypes-#LPO-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT→BOOL a₁ a₂
                          → equalTypes n w (#LPO-right a₁) (#LPO-right a₂)
→equalTypes-#LPO-right {n} {w} {a₁} {a₂} eqt =
  eqTypesPI← (λ w' _ → eqTypesNAT) aw1
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



isTypeLPO-PI : (w : 𝕎·) (n : ℕ) → isType n w #LPO-PI
isTypeLPO-PI w n =
  eqTypesPI← {w} {n}
              {#NAT→BOOL} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)}
              {#NAT→BOOL} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)}
              (λ w' e → isType-#NAT→BOOL w' n)
              aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT→BOOL a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)))
                                         (sub0 a₂ (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))))
    aw w' e a₁ a₂ eqb rewrite sub0-squash-union-LPO a₁ | sub0-squash-union-LPO a₂ = eqt
      where
        eqt1 : equalTypes n w' (#LPO-left a₁) (#LPO-left a₂)
        eqt1 = →equalTypes-#LPO-left eqb

        eqt2 : equalTypes n w' (#LPO-right a₁) (#LPO-right a₂)
        eqt2 = →equalTypes-#LPO-right eqb

        eqt : equalTypes n w' (#SQUASH (#UNION (#LPO-left a₁) (#LPO-right a₁))) (#SQUASH (#UNION (#LPO-left a₂) (#LPO-right a₂)))
        eqt = eqTypesSQUASH← (eqTypesUNION← eqt1 eqt2)



isTypeLPO : (w : 𝕎·) (n : ℕ) → isType n w #LPO
isTypeLPO w n rewrite #LPO≡#PI = isTypeLPO-PI w n


isTypeNegLPO : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #LPO)
isTypeNegLPO w n = eqTypesNEG← (isTypeLPO w n)



#LPO-left→#Σchoice : Boolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                      → compatible· name w Resℂ
                      → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                      → inhType n w (#LPO-left (#CS name))
                      → inhType n w (#Σchoice name ℂ₁·)
#LPO-left→#Σchoice bcb {n} {w} {name} comp sat (t , inh) =
  t , ≡CTerm→equalInType
        (sym (#Σchoice≡ name ℂ₁·))
        (fun-equalInType-SUM-NAT {n} {w} {#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR)} aw1 aw2 inh)
  where
    aw1 : ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #NAT m
                        → equalInType n w' (sub0 m (#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR))) t₁ t₂
                        → equalInType n w' (sub0 m (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)) t₁ t₂)
    aw1 w1 e1 m t₁ t₂ j eqi = ≡CTerm→equalInType (sym (sub0-#Σchoice-body≡ m name ℂ₁·)) eqi2
      where
        eqi1 : equalInType n w1 (#ASSERT₂ (#APPLY (#CS name) m)) t₁ t₂
        eqi1 = ≡CTerm→equalInType (sub0-ASSERT-APPLY m (#CS name)) eqi

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #BOOL) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-BOOL-Typeℂ₀₁ n w1 bcb)
                          (→equalInType-APPLY-CS-BOOL bcb (⊑-compatible· e1 comp) j)
                          (equalInType-BTRUE-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₂≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat



#LPO-right→#Σchoice : Boolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                      → compatible· name w Resℂ
                      → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                      → inhType n w (#LPO-right (#CS name))
                      → inhType n w (#NEG (#Σchoice name ℂ₁·))
#LPO-right→#Σchoice bcb {n} {w} {name} comp sat (f , inh) =
  #lamAX , equalInType-NEG aw1 aw2
  where
    aw0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR)))) (#APPLY f a₁) (#APPLY f a₂))
    aw0 = snd (snd (equalInType-PI→ {n} {w} {#NAT} {#[0]NEG (#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR))} inh))

    aw1 : ∀𝕎 w λ w1 e1 → isType n w1 (#Σchoice name ℂ₁·)
    aw1 w1 e1 = equalInType-#Σchoice w1 name ℂ₁· (⊑-compatible· e1 comp) sat

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#Σchoice name ℂ₁·) a₁ a₂)
    aw2 w1 e1 p₁ p₂ eqi = lower (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI aw3 h1))
      where
        aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #NAT)
                                      (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                      w' p₁ p₂
                             → Lift (lsuc L) ⊥)
        aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (eqi3 eqi4)
          where
            eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi2 : equalInType n w2 (#NEG (#ASSERT₂ (#APPLY (#CS name) a₁))) (#APPLY f a₁) (#APPLY f a₂)
            eqi2 = ≡CTerm→equalInType (sub0-NEG-ASSERT-APPLY a₁ (#CS name)) (aw0 w2 (⊑-trans· e1 e2) a₁ a₂ ea)

            eqi3 : ¬ equalInType n w2 (#ASSERT₂ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi3 = equalInType-NEG→ eqi2 w2 (⊑-refl· _) b₁ b₂

            eqi4 : equalInType n w2 (#ASSERT₂ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi4 = ≡CTerm→equalInType (trans (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd bcb)) (fst bcb))
                                              (sym (#ASSERT₂≡ (#APPLY (#CS name) a₁))))
                                       eqi1

        h0 : equalInType n w1 (#SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) p₁ p₂
        h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) eqi

        h1 : inbar w1 (λ w' _ → SUMeq (equalInType n w' #NAT) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' p₁ p₂)
        h1 = equalInType-SUM→ h0




-- Assuming that our choices are Bools
¬LPO : Boolℂ CB → (w : 𝕎·) → member w (#NEG #LPO) #lamAX
¬LPO bcb w = n , equalInType-NEG (λ w1 e1 → isTypeLPO w1 n) aw1
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
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT→BOOL f g
                             → equalInType n w' (sub0 f (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT→BOOL} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT→BOOL f g
                             → equalInType n w' (#SQUASH (#UNION (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G g))
        aw3 w' e f g ex = ≡CTerm→equalInType (sub0-squash-union-LPO f) (aw2 w' e f g ex)

        name : Name
        name = newChoice· w1

        w2 : 𝕎·
        w2 = startNewChoice Resℂ w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏· Resℂ w1

        comp1 : compatible· name w2 Resℂ
        comp1 = startChoiceCompatible· Resℂ w1

        h : ¬ equalInType n w2 (sq-dec (#Σchoice name ℂ₁·)) #AX #AX
        h = ¬-dec-Σchoice w1 n

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT n w' m))

        eqf1 : ∈Type n w2 #NAT→BOOL f
        eqf1 = →equalInType-CS-NAT→BOOL eqf2

        h1 : equalInType n w2 (#SQUASH (#UNION (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G f)
        h1 = aw3 w2 e2 f f eqf1

        imp1 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-left f) → inhType n w' (#Σchoice name ℂ₁·))
        imp1 w3 e3 inh = #LPO-left→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh

        imp2 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-right f) → inhType n w' (#NEG (#Σchoice name ℂ₁·)))
        imp2 w3 e3 inh = #LPO-right→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh

\end{code}[hide]
