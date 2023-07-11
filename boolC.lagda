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
open import encode


module boolC {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
             (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
             (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
             (N : NewChoice {L} W C K G)
             (EC : Encode)
             (V : ChoiceVal W C K G X N EC)
             (F : Freeze {L} W C K P G N)
             (E : Extensionality 0ℓ (lsuc(lsuc(L))))
             (CB : ChoiceBar W M C K P G X N EC V F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(EC)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)



-- If we only want to consider Boolean choices, where ℂ₀ stands for false, and ℂ₁ stands for true
Bool₀ℂ : ChoiceBar W M C K P G X N EC V F E → Set
Bool₀ℂ cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #BOOL₀
  × Cℂ₀ ≡ #BFALSE
  × Cℂ₁ ≡ #BTRUE


Bool₀!ℂ : ChoiceBar W M C K P G X N EC V F E → Set
Bool₀!ℂ cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #BOOL₀!
  × Cℂ₀ ≡ #BFALSE
  × Cℂ₁ ≡ #BTRUE


Bool!ℂ : ChoiceBar W M C K P G X N EC V F E → Set
Bool!ℂ cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #BOOL!
  × Cℂ₀ ≡ #BFALSE
  × Cℂ₁ ≡ #BTRUE


equalTypes-BOOL-Typeℂ₀₁ : Bool₀ℂ CB → (n : ℕ) (w : 𝕎·)
                          → equalTypes n w #BOOL₀ Typeℂ₀₁·
equalTypes-BOOL-Typeℂ₀₁ bcb n w rewrite fst bcb = isTypeBOOL₀


equalTypes-BOOL₀!-Typeℂ₀₁ : Bool₀!ℂ CB → (n : ℕ) (w : 𝕎·)
                          → equalTypes n w #BOOL₀! Typeℂ₀₁·
equalTypes-BOOL₀!-Typeℂ₀₁ bcb n w rewrite fst bcb = isTypeBOOL₀!→ n w


equalTypes-BOOL!-Typeℂ₀₁ : Bool!ℂ CB → (n : ℕ) (w : 𝕎·)
                          → equalTypes n w #BOOL! Typeℂ₀₁·
equalTypes-BOOL!-Typeℂ₀₁ bcb n w rewrite fst bcb = isTypeBOOL! w n



→equalInType-APPLY-CS-BOOL : Bool₀ℂ CB → {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                              → compatible· c w Resℂ
                              → equalInType i w #NAT! a₁ a₂
                              → equalInType i w #BOOL₀ (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-BOOL bcb {i} {w} {c} {a₁} {a₂} comp eqi =
  ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· comp eqi)



→equalInType-APPLY-CS-BOOL₀! : Bool₀!ℂ CB → {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                               → compatible· c w Resℂ
                               → equalInType i w #NAT! a₁ a₂
                               → equalInType i w #BOOL₀! (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-BOOL₀! bcb {i} {w} {c} {a₁} {a₂} comp eqi =
  ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· comp eqi)



→equalInType-APPLY-CS-BOOL! : Bool!ℂ CB → {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                               → compatible· c w Resℂ
                               → equalInType i w #NAT! a₁ a₂
                               → equalInType i w #BOOL! (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-BOOL! bcb {i} {w} {c} {a₁} {a₂} comp eqi =
  ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· comp eqi)


equalInType-BTRUE₀-ℂ₁ : Bool₀ℂ CB → (n : ℕ) (w : 𝕎·) → equalInType n w #BOOL₀ #BTRUE Cℂ₁
equalInType-BTRUE₀-ℂ₁ bcb n w rewrite snd (snd bcb) = BTRUE∈BOOL₀ n w


equalInType-BTRUE₀!-ℂ₁ : Bool₀!ℂ CB → (n : ℕ) (w : 𝕎·) → equalInType n w #BOOL₀! #BTRUE Cℂ₁
equalInType-BTRUE₀!-ℂ₁ bcb n w rewrite snd (snd bcb) = →equalInType-BOOL₀!-INL n w #AX #AX


equalInType-BTRUE!-ℂ₁ : Bool!ℂ CB → (n : ℕ) (w : 𝕎·) → equalInType n w #BOOL! #BTRUE Cℂ₁
equalInType-BTRUE!-ℂ₁ bcb n w rewrite snd (snd bcb) = BTRUE∈BOOL! n w


#SUM-ASSERT₂→#Σchoice : Bool₀ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
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

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #BOOL₀) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-BOOL-Typeℂ₀₁ bcb n w1)
                          (→equalInType-APPLY-CS-BOOL bcb (⊑-compatible· e1 comp) j)
                          (equalInType-BTRUE₀-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₂≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT! a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat



#SUM-ASSERT₃→#Σchoice : Bool!ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
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

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #BOOL!) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-BOOL!-Typeℂ₀₁ bcb n w1)
                          (→equalInType-APPLY-CS-BOOL! bcb (⊑-compatible· e1 comp) j)
                          (equalInType-BTRUE!-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₃≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT! a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat


#SUM-ASSERT₅→#Σchoice : Bool₀!ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                       → compatible· name w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                       → inhType n w (#SUM-ASSERT₅ (#CS name))
                       → inhType n w (#Σchoice name ℂ₁·)
#SUM-ASSERT₅→#Σchoice bcb {n} {w} {name} comp sat (t , inh) =
  t , ≡CTerm→equalInType
        (sym (#Σchoice≡ name ℂ₁·))
        (fun-equalInType-SUM-NAT! {n} {w} {#[0]ASSERT₄ (#[0]APPLY (#[0]CS name) #[0]VAR)} aw1 aw2 inh)
  where
    aw1 : ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #NAT! m
                       → equalInType n w' (sub0 m (#[0]ASSERT₄ (#[0]APPLY (#[0]CS name) #[0]VAR))) t₁ t₂
                       → equalInType n w' (sub0 m (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)) t₁ t₂)
    aw1 w1 e1 m t₁ t₂ j eqi = ≡CTerm→equalInType (sym (sub0-#Σchoice-body≡ m name ℂ₁·)) eqi2
      where
        eqi1 : equalInType n w1 (#ASSERT₄ (#APPLY (#CS name) m)) t₁ t₂
        eqi1 = ≡CTerm→equalInType (sub0-ASSERT₄-APPLY m (#CS name)) eqi

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #BOOL₀!) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-BOOL₀!-Typeℂ₀₁ bcb n w1)
                         (→equalInType-APPLY-CS-BOOL₀! bcb (⊑-compatible· e1 comp) j)
                         (equalInType-BTRUE₀!-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₄≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT! a₁ a₂)
                       → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                         (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat



#PI-NEG-ASSERT₂→#Σchoice : Bool₀ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
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



#PI-NEG-ASSERT₃→#Σchoice : Bool!ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
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
