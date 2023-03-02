\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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


module boolC {L : Level} (L' : Level) (W : PossibleWorlds {L}) (M : Mod L' W)
             (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
             (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
             (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
             (F : Freeze {L} W C K P G N)
             (E : Extensionality 0ℓ (lsuc (lsuc L) ⊔ lsuc (lsuc L')))
             (CB : ChoiceBar L' W M C K P G X N V F E)
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
open import bar(L')(W)
open import barI(L')(W)(M)--(C)(K)(P)
open import forcing(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceBarDef(L')(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(L')(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(L')(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



-- If we only want to consider Boolean choices, where ℂ₀ stands for false, and ℂ₁ stands for true
Boolℂ : ChoiceBar L' W M C K P G X N V F E → Set
Boolℂ cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #BOOL
  × Cℂ₀ ≡ #BFALSE
  × Cℂ₁ ≡ #BTRUE


QTBoolℂ : ChoiceBar L' W M C K P G X N V F E → Set
QTBoolℂ cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #QTBOOL!
  × Cℂ₀ ≡ #BFALSE
  × Cℂ₁ ≡ #BTRUE



equalTypes-BOOL-Typeℂ₀₁ : Boolℂ CB → (n : ℕ) (w : 𝕎·)
                          → equalTypes n w #BOOL Typeℂ₀₁·
equalTypes-BOOL-Typeℂ₀₁ bcb n w rewrite fst bcb = isTypeBOOL w n



equalTypes-QTBOOL!-Typeℂ₀₁ : QTBoolℂ CB → (n : ℕ) (w : 𝕎·)
                          → equalTypes n w #QTBOOL! Typeℂ₀₁·
equalTypes-QTBOOL!-Typeℂ₀₁ bcb n w rewrite fst bcb = eqTypesQTBOOL! {w} {n}



→equalInType-APPLY-CS-BOOL : Boolℂ CB → {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                              → compatible· c w Resℂ
                              → equalInType i w #NAT! a₁ a₂
                              → equalInType i w #BOOL (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-BOOL bcb {i} {w} {c} {a₁} {a₂} comp eqi =
  ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· comp eqi)



→equalInType-APPLY-CS-QTBOOL! : QTBoolℂ CB → {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                               → compatible· c w Resℂ
                               → equalInType i w #NAT! a₁ a₂
                               → equalInType i w #QTBOOL! (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-QTBOOL! bcb {i} {w} {c} {a₁} {a₂} comp eqi =
  ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· comp eqi)



equalInType-BTRUE-ℂ₁ : Boolℂ CB → (n : ℕ) (w : 𝕎·) → equalInType n w #BOOL #BTRUE Cℂ₁
equalInType-BTRUE-ℂ₁ bcb n w rewrite snd (snd bcb) = BTRUE∈BOOL n w



equalInType-QT-BTRUE-ℂ₁ : QTBoolℂ CB → (n : ℕ) (w : 𝕎·) → equalInType n w #QTBOOL! #BTRUE Cℂ₁
equalInType-QT-BTRUE-ℂ₁ bcb n w rewrite snd (snd bcb) = BTRUE∈QTBOOL! n w



#SUM-ASSERT₂ : CTerm → CTerm
#SUM-ASSERT₂ f = #SUM #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#PI-NEG-ASSERT₂ : CTerm → CTerm
#PI-NEG-ASSERT₂ f = #PI #NAT! (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))



#SUM-ASSERT₃ : CTerm → CTerm
#SUM-ASSERT₃ f = #SUM #NAT! (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#PI-NEG-ASSERT₃ : CTerm → CTerm
#PI-NEG-ASSERT₃ f = #PI #NAT! (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))



→equalTypes-#SUM-ASSERT₂ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT!→BOOL a₁ a₂
                           → equalTypes n w (#SUM-ASSERT₂ a₁) (#SUM-ASSERT₂ a₂)
→equalTypes-#SUM-ASSERT₂ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₂-APPLY a a₁ | sub0-ASSERT₂-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₂ (#APPLY a₁ a)) (#ASSERT₂ (#APPLY a₂ b))
        aw2 = equalInType-BOOL→equalTypes-ASSERT₂ eqb



→equalTypes-#SUM-ASSERT₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT!→QTBOOL! a₁ a₂
                           → equalTypes n w (#SUM-ASSERT₃ a₁) (#SUM-ASSERT₃ a₂)
→equalTypes-#SUM-ASSERT₃ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₃-APPLY a a₁ | sub0-ASSERT₃-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₃ (#APPLY a₁ a)) (#ASSERT₃ (#APPLY a₂ b))
        aw2 = equalInType-QTBOOL!→equalTypes-ASSERT₃ eqb



→equalTypes-#PI-NEG-ASSERT₂ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                              → equalInType n w #NAT!→BOOL a₁ a₂
                              → equalTypes n w (#PI-NEG-ASSERT₂ a₁) (#PI-NEG-ASSERT₂ a₂)
→equalTypes-#PI-NEG-ASSERT₂ {n} {w} {a₁} {a₂} eqt =
  eqTypesPI← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                          (sub0 b (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR)))))
    aw1 w' e a b ea rewrite sub0-NEG-ASSERT₂-APPLY a a₁ | sub0-NEG-ASSERT₂-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#NEG (#ASSERT₂ (#APPLY a₁ a))) (#NEG (#ASSERT₂ (#APPLY a₂ b)))
        aw2 = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT₂ eqb)



→equalTypes-#PI-NEG-ASSERT₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                              → equalInType n w #NAT!→QTBOOL! a₁ a₂
                              → equalTypes n w (#PI-NEG-ASSERT₃ a₁) (#PI-NEG-ASSERT₃ a₂)
→equalTypes-#PI-NEG-ASSERT₃ {n} {w} {a₁} {a₂} eqt =
  eqTypesPI← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                          (sub0 b (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR)))))
    aw1 w' e a b ea rewrite sub0-NEG-ASSERT₃-APPLY a a₁ | sub0-NEG-ASSERT₃-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#NEG (#ASSERT₃ (#APPLY a₁ a))) (#NEG (#ASSERT₃ (#APPLY a₂ b)))
        aw2 = eqTypesNEG← (equalInType-QTBOOL!→equalTypes-ASSERT₃ eqb)



#SUM-ASSERT₂→#Σchoice : Boolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                       → compatible· name w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                       → inhType n w (#SUM-ASSERT₂ (#CS name))
                       → inhType n w (#Σchoice name ℂ₁·)
#SUM-ASSERT₂→#Σchoice bcb {n} {w} {name} comp sat (t , inh) =
  t , ≡CTerm→equalInType
        (sym (#Σchoice≡ name ℂ₁·))
        (fun-equalInType-SUM-NAT! {n} {w} {#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR)} aw1 aw2 inh)
  where
    aw1 : ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #NAT! m
                        → equalInType n w' (sub0 m (#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR))) t₁ t₂
                        → equalInType n w' (sub0 m (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)) t₁ t₂)
    aw1 w1 e1 m t₁ t₂ j eqi = ≡CTerm→equalInType (sym (sub0-#Σchoice-body≡ m name ℂ₁·)) eqi2
      where
        eqi1 : equalInType n w1 (#ASSERT₂ (#APPLY (#CS name) m)) t₁ t₂
        eqi1 = ≡CTerm→equalInType (sub0-ASSERT₂-APPLY m (#CS name)) eqi

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #BOOL) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-BOOL-Typeℂ₀₁ bcb n w1)
                          (→equalInType-APPLY-CS-BOOL bcb (⊑-compatible· e1 comp) j)
                          (equalInType-BTRUE-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₂≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT! a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat



#SUM-ASSERT₃→#Σchoice : QTBoolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                       → compatible· name w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                       → inhType n w (#SUM-ASSERT₃ (#CS name))
                       → inhType n w (#Σchoice name ℂ₁·)
#SUM-ASSERT₃→#Σchoice bcb {n} {w} {name} comp sat (t , inh) =
  t , ≡CTerm→equalInType
        (sym (#Σchoice≡ name ℂ₁·))
        (fun-equalInType-SUM-NAT! {n} {w} {#[0]ASSERT₃ (#[0]APPLY (#[0]CS name) #[0]VAR)} aw1 aw2 inh)
  where
    aw1 : ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #NAT! m
                        → equalInType n w' (sub0 m (#[0]ASSERT₃ (#[0]APPLY (#[0]CS name) #[0]VAR))) t₁ t₂
                        → equalInType n w' (sub0 m (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)) t₁ t₂)
    aw1 w1 e1 m t₁ t₂ j eqi = ≡CTerm→equalInType (sym (sub0-#Σchoice-body≡ m name ℂ₁·)) eqi2
      where
        eqi1 : equalInType n w1 (#ASSERT₃ (#APPLY (#CS name) m)) t₁ t₂
        eqi1 = ≡CTerm→equalInType (sub0-ASSERT₃-APPLY m (#CS name)) eqi

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #QTBOOL!) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-QTBOOL!-Typeℂ₀₁ bcb n w1)
                          (→equalInType-APPLY-CS-QTBOOL! bcb (⊑-compatible· e1 comp) j)
                          (equalInType-QT-BTRUE-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₃≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT! a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat



#PI-NEG-ASSERT₂→#Σchoice : Boolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                          → compatible· name w Resℂ
                          → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                          → inhType n w (#PI-NEG-ASSERT₂ (#CS name))
                          → inhType n w (#NEG (#Σchoice name ℂ₁·))
#PI-NEG-ASSERT₂→#Σchoice bcb {n} {w} {name} comp sat (f , inh) =
  #lamAX , equalInType-NEG aw1 aw2
  where
    aw0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR)))) (#APPLY f a₁) (#APPLY f a₂))
    aw0 = snd (snd (equalInType-PI→ {n} {w} {#NAT!} {#[0]NEG (#[0]ASSERT₂ (#[0]APPLY (#[0]CS name) #[0]VAR))} inh))

    aw1 : isType n w (#Σchoice name ℂ₁·)
    aw1 = equalInType-#Σchoice w name ℂ₁· comp sat

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#Σchoice name ℂ₁·) a₁ a₂)
    aw2 w1 e1 p₁ p₂ eqi = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
      where
        aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #NAT!)
                                      (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                      w' p₁ p₂
                             → Lift (lsuc L) ⊥)
        aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (eqi3 eqi4)
          where
            eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi2 : equalInType n w2 (#NEG (#ASSERT₂ (#APPLY (#CS name) a₁))) (#APPLY f a₁) (#APPLY f a₂)
            eqi2 = ≡CTerm→equalInType (sub0-NEG-ASSERT₂-APPLY a₁ (#CS name)) (aw0 w2 (⊑-trans· e1 e2) a₁ a₂ ea)

            eqi3 : ¬ equalInType n w2 (#ASSERT₂ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi3 = equalInType-NEG→ eqi2 w2 (⊑-refl· _) b₁ b₂

            eqi4 : equalInType n w2 (#ASSERT₂ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi4 = ≡CTerm→equalInType (trans (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd bcb)) (fst bcb))
                                              (sym (#ASSERT₂≡ (#APPLY (#CS name) a₁))))
                                       eqi1

        h0 : equalInType n w1 (#SUM #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) p₁ p₂
        h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) eqi

        h1 : □· w1 (λ w' _ → SUMeq (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' p₁ p₂)
        h1 = equalInType-SUM→ h0



#PI-NEG-ASSERT₃→#Σchoice : QTBoolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                          → compatible· name w Resℂ
                          → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                          → inhType n w (#PI-NEG-ASSERT₃ (#CS name))
                          → inhType n w (#NEG (#Σchoice name ℂ₁·))
#PI-NEG-ASSERT₃→#Σchoice bcb {n} {w} {name} comp sat (f , inh) =
  #lamAX , equalInType-NEG aw1 aw2
  where
    aw0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY (#[0]CS name) #[0]VAR)))) (#APPLY f a₁) (#APPLY f a₂))
    aw0 = snd (snd (equalInType-PI→ {n} {w} {#NAT!} {#[0]NEG (#[0]ASSERT₃ (#[0]APPLY (#[0]CS name) #[0]VAR))} inh))

    aw1 : isType n w (#Σchoice name ℂ₁·)
    aw1 = equalInType-#Σchoice w name ℂ₁· comp sat

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#Σchoice name ℂ₁·) a₁ a₂)
    aw2 w1 e1 p₁ p₂ eqi = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
      where
        aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #NAT!)
                                      (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                      w' p₁ p₂
                             → Lift (lsuc L) ⊥)
        aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (eqi3 eqi4)
          where
            eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi2 : equalInType n w2 (#NEG (#ASSERT₃ (#APPLY (#CS name) a₁))) (#APPLY f a₁) (#APPLY f a₂)
            eqi2 = ≡CTerm→equalInType (sub0-NEG-ASSERT₃-APPLY a₁ (#CS name)) (aw0 w2 (⊑-trans· e1 e2) a₁ a₂ ea)

            eqi3 : ¬ equalInType n w2 (#ASSERT₃ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi3 = equalInType-NEG→ eqi2 w2 (⊑-refl· _) b₁ b₂

            eqi4 : equalInType n w2 (#ASSERT₃ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi4 = ≡CTerm→equalInType (trans (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd bcb)) (fst bcb))
                                              (sym (#ASSERT₃≡ (#APPLY (#CS name) a₁))))
                                       eqi1

        h0 : equalInType n w1 (#SUM #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) p₁ p₂
        h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) eqi

        h1 : □· w1 (λ w' _ → SUMeq (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' p₁ p₂)
        h1 = equalInType-SUM→ h0

\end{code}
