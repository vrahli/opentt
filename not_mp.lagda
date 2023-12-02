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
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst ; cong ; cong₂)
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


module not_mp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (subv# ; →#shiftUp)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (≡EQ ; ≡APPLY)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (#APPLY2)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#strongMonEq-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqInType-ext ; TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-PI→ ; ≡CTerm→equalInType ; NUM-equalInType-NAT! ; equalInType-FUN→ ; equalInType-SQUASH→ ;
         equalInType-NEG ; equalInType-SUM→ ; equalInType-refl ; equalInType-mon ; →≡equalInType ; equalInType-SUM ;
         isTypeNAT! ; →≡equalTypes ; eqTypesFUN← ; equalInType-NEG→ ; eqTypesNEG← ; eqTypesSQUASH← ; eqTypesNAT ;
         eqTypesNOWRITE ; eqTypesQNAT ; wPredExtIrr-eqInType ; equalInType-NAT!→ ; eqTypesNOREAD ; #⇛val→#⇓→#⇛ ;
         #strongMonEq→#weakMonEq ; equalInType-local ; ≡CTerm→eqTypes ; eqTypesEQ← ; ¬equalInType-FALSE)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-CS-NAT!→BOOL₀ ; equalInType-NEG→¬inh ; equalInType-NEG-inh ; sub0-ASSERT₃-APPLY ;
         →equalInType-CS-NAT!→BOOL! ; →equalInType-CS-NAT!→BOOL₀! ; isType-#NAT!→BOOL₀ ; →equalInType-SQUASH ;
         →equalInType-CS-NAT!→T ; equalTerms-pres-#⇛-left-rev ; equalInType-EQ→₁ ; equalTypes-#⇛-left-right-rev ;
         →equalInType-TRUE ; equalTypes-#⇛-left-right ; equalInType-#⇛-LR ; inhType-mon)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-SUM!→ ; SUMeq! ; equalInType-SUM! ; _#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ;
         →equalInType-EQ)
--open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalTerms-pres-#⇛-left-BOOL! ; equalTerms-pres-#⇛-left-rev-BOOL!)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)

open import type_sys_props_isect(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqInType-⇛-ISECT-rev)


alwaysFreezable : Freeze W C K P G N → Set(L)
alwaysFreezable f = (c : Name) (w : 𝕎·) → Freeze.freezable f c w


-- Assuming that our choices are Bools
-- and that choices are always freezable (see where it is used below)
-- Boolℂ CB is for BOOL, which then would be only for FCSs, not references, which change over time
¬MP : Bool₀ℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP) #lamAX
¬MP bcb afb w n = equalInType-NEG (isTypeMP w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→BOOL₀ f g
                             → equalInType n w' (sub0 f (#[0]FUN #[0]MP-left #[0]MP-right)) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left #[0]MP-right} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→BOOL₀ f g
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

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL₀ (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→BOOL₀ f
        eqf1 = →equalInType-CS-NAT!→BOOL₀ eqf2

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
        w3 = fst (followChoice· name h5 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (followChoice· name h5 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
        oc2 = fst (snd (snd (followChoice· name h5 oc1 comp1 fb1)))

        comp2 : compatible· name w3 Resℂ
        comp2 = fst (snd (snd (snd (followChoice· name h5 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (followChoice· name h5 oc1 comp1 fb1)))))

        h6 : inhType n w3 (#SUM-ASSERT₂ f)
        h6 = snd (snd (snd (snd (snd (followChoice· name h5 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice name ℂ₁·)
        h7 = #SUM-ASSERT₂→#Σchoice bcb comp2 (0 , sat-ℂ₁ 0) h6

        h8 : ¬ inhType n w3 (#Σchoice name ℂ₁·)
        h8 = ¬equalInType-#Σchoice n w3 Resℂ name isValueℂ₀· isValueℂ₁· ¬∼ℂ₀₁· oc2 comp2 fb2


¬ΣNAT!→¬inhType-Σchoice₃ : Bool!ℂ CB → (n : ℕ) (w : 𝕎·) (name : Name)
                           → ∀𝕎 w (λ w' _ → ¬ Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₃ (#APPLY (#CS name) n₁)))))
                           → ∀𝕎 w (λ w' _ → ¬ inhType n w' (#Σchoice name ℂ₁·))
¬ΣNAT!→¬inhType-Σchoice₃ bcb n w name aw w1 e1 (t , inh) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
  where
    h0 : ∈Type n w1 (#SUM #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) t
    h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) inh

    h1 : □· w1 (λ w' _ → SUMeq (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' t t)
    h1 = equalInType-SUM→ h0

    aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #NAT!)
                                   (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                   w' t t
                          → Lift (lsuc L) ⊥)
    aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (aw w2 (⊑-trans· e1 e2) (a₁ , a₂ , ea , b₁ , equalInType-refl eqi2))
          where
            eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi2 : equalInType n w2 (#ASSERT₃ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi2 = ≡CTerm→equalInType (trans (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd bcb)) (fst bcb))
                                              (sym (#ASSERT₃≡ (#APPLY (#CS name) a₁))))
                                       eqi1


ΣinhType-ASSERT₃→inhType-SUM-ASSERT₃ : (n : ℕ) (w : 𝕎·) (f : CTerm)
                                        → ∈Type n w #NAT!→BOOL! f
                                        → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w #NAT! n₁ n₂
                                            × inhType n w (#ASSERT₃ (#APPLY f n₁))))
                                        → inhType n w (#SUM-ASSERT₃ f)
ΣinhType-ASSERT₃→inhType-SUM-ASSERT₃ n w f f∈ (n₁ , n₂ , n∈ , (t , inh)) =
  #PAIR n₁ t ,
  equalInType-SUM
    (λ w' _ → isTypeNAT!)
    (isType-MP-right-qt-body n w f f f∈)
    (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType n w' #NAT!)
                                (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                w' (#PAIR n₁ t) (#PAIR n₁ t))
    aw w1 e1 =
      n₁ , n₁ , t , t , equalInType-refl (equalInType-mon n∈ w1 e1) ,
      ⇓-refl ⌜ #PAIR n₁ t ⌝ w1 , --#⇛-refl w1 (#PAIR n₁ t) ,
      ⇓-refl ⌜ #PAIR n₁ t ⌝ w1 , --#⇛-refl w1 (#PAIR n₁ t) ,
      →≡equalInType (sym (sub0-ASSERT₃-APPLY n₁ f)) (equalInType-mon inh w1 e1)


-- QTBool!ℂ CB is for QTBOOL! which works for FCSs and refs
¬MP₄ : Bool!ℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₄) #lamAX
¬MP₄ bcb afb w n = equalInType-NEG (isTypeMP₄ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP₄ a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type n w' #NAT!→BOOL! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                                  × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERT₃ (#APPLY f n₁))))))
        aw2 = ∈#MP₄→ n w1 F G ea

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

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→BOOL! f
        eqf1 = →equalInType-CS-NAT!→BOOL! eqf2

        h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                   × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
                                               → ⊥)
                             → ⊥)
        h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice n w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (afb name w3) z
          where
            z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType n w4 (#Σchoice name ℂ₁·))
            z = ¬ΣNAT!→¬inhType-Σchoice₃ bcb n w3 name aw

        h4 : □· w2 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
        h4 = aw2 w2 e2 f eqf1 h3

        -- We follow the choice
        w3 : 𝕎·
        w3 = fst (followChoice· name h4 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (followChoice· name h4 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
        oc2 = fst (snd (snd (followChoice· name h4 oc1 comp1 fb1)))

        comp2 : compatible· name w3 Resℂ
        comp2 = fst (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

        h6 : Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w3 #NAT! n₁ n₂
              × inhType n w3 (#ASSERT₃ (#APPLY f n₁))))
        h6 = snd (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice name ℂ₁·)
        h7 = #SUM-ASSERT₃→#Σchoice bcb comp2 (0 , sat-ℂ₁ 0) (ΣinhType-ASSERT₃→inhType-SUM-ASSERT₃ n w3 f (equalInType-mon eqf1 w3 e3) h6)

        h8 : ¬ inhType n w3 (#Σchoice name ℂ₁·)
        h8 = ¬equalInType-#Σchoice n w3 Resℂ name isValueℂ₀· isValueℂ₁· ¬∼ℂ₀₁· oc2 comp2 fb2


¬ΣNAT!→¬inhType-Σchoice₄ : Bool₀!ℂ CB → (n : ℕ) (w : 𝕎·) (name : Name)
                           → ∀𝕎 w (λ w' _ → ¬ Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₄ (#APPLY (#CS name) n₁)))))
                           → ∀𝕎 w (λ w' _ → ¬ inhType n w' (#Σchoice name ℂ₁·))
¬ΣNAT!→¬inhType-Σchoice₄ bcb n w name aw w1 e1 (t , inh) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
  where
    h0 : ∈Type n w1 (#SUM #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) t
    h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) inh

    h1 : □· w1 (λ w' _ → SUMeq (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' t t)
    h1 = equalInType-SUM→ h0

    aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #NAT!)
                                   (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                   w' t t
                          → Lift (lsuc L) ⊥)
    aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (aw w2 (⊑-trans· e1 e2) (a₁ , a₂ , ea , b₁ , equalInType-refl eqi2))
          where
            eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi2 : equalInType n w2 (#ASSERT₄ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi2 = ≡CTerm→equalInType (trans (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd bcb)) (fst bcb))
                                              (sym (#ASSERT₄≡ (#APPLY (#CS name) a₁))))
                                       eqi1


ΣinhType-ASSERT₄→inhType-SUM-ASSERT₅ : (n : ℕ) (w : 𝕎·) (f : CTerm)
                                        → ∈Type n w #NAT!→BOOL₀! f
                                        → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w #NAT! n₁ n₂
                                            × inhType n w (#ASSERT₄ (#APPLY f n₁))))
                                        → inhType n w (#SUM-ASSERT₅ f)
ΣinhType-ASSERT₄→inhType-SUM-ASSERT₅ n w f f∈ (n₁ , n₂ , n∈ , (t , inh)) =
  #PAIR n₁ t ,
  equalInType-SUM
    (λ w' _ → isTypeNAT!)
    (isType-MP-right-qt₃-body n w f f f∈)
    (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType n w' #NAT!)
                                (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                w' (#PAIR n₁ t) (#PAIR n₁ t))
    aw w1 e1 =
      n₁ , n₁ , t , t , equalInType-refl (equalInType-mon n∈ w1 e1) ,
      ⇓-refl ⌜ #PAIR n₁ t ⌝ w1 , --#⇛-refl w1 (#PAIR n₁ t) ,
      ⇓-refl ⌜ #PAIR n₁ t ⌝ w1 , --#⇛-refl w1 (#PAIR n₁ t) ,
      →≡equalInType (sym (sub0-ASSERT₄-APPLY n₁ f)) (equalInType-mon inh w1 e1)


-- Bool₀!ℂ CB is for BOOL₀! which works only for FCSs
-- There is an instantiation in modInstanceBethCsBool2.lagda
-- alwaysFreezable is also for FCSs
-- This version uses truncated Σs, and noread/nowrite ℕ and 𝔹
¬MP₆ : Bool₀!ℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₆) #lamAX
¬MP₆ bcb afb w n = equalInType-NEG (isTypeMP₆ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP₆ a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type n w' #NAT!→BOOL₀! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                                  × inhType n w' (#ASSERT₄ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERT₄ (#APPLY f n₁))))))
        aw2 = ∈#MP₆→ n w1 F G ea

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

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL₀! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (proj₁ bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→BOOL₀! f
        eqf1 = →equalInType-CS-NAT!→BOOL₀! eqf2

        h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                   × inhType n w' (#ASSERT₄ (#APPLY f n₁)))))
                                               → ⊥)
                             → ⊥)
        h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice n w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (afb name w3) z
          where
            z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType n w4 (#Σchoice name ℂ₁·))
            z = ¬ΣNAT!→¬inhType-Σchoice₄ bcb n w3 name aw

        h4 : □· w2 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERT₄ (#APPLY f n₁)))))
        h4 = aw2 w2 e2 f eqf1 h3

        -- We follow the choice
        w3 : 𝕎·
        w3 = fst (followChoice· name h4 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (followChoice· name h4 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
        oc2 = fst (snd (snd (followChoice· name h4 oc1 comp1 fb1)))

        comp2 : compatible· name w3 Resℂ
        comp2 = fst (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

        h6 : Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w3 #NAT! n₁ n₂
              × inhType n w3 (#ASSERT₄ (#APPLY f n₁))))
        h6 = snd (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice name ℂ₁·)
        h7 = #SUM-ASSERT₅→#Σchoice bcb comp2 (0 , sat-ℂ₁ 0) (ΣinhType-ASSERT₄→inhType-SUM-ASSERT₅ n w3 f (equalInType-mon eqf1 w3 e3) h6)

        h8 : ¬ inhType n w3 (#Σchoice name ℂ₁·)
        h8 = ¬equalInType-#Σchoice n w3 Resℂ name isValueℂ₀· isValueℂ₁· ¬∼ℂ₀₁· oc2 comp2 fb2


equalInType-#MP-rightₘ→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                        → equalInType i w (#MP-rightₘ f) a₁ a₂
                        → □· w (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                         × inhType i w' (#ASSERTₘ (#APPLY f n₁)))))
equalInType-#MP-rightₘ→ i w f a₁ a₂ h =
  Mod.∀𝕎-□Func M aw (equalInType-SUM!→ h)
  where
  aw : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' #NAT!)
                              (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                              w' a₁ a₂
                     → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂ × inhType i w' (#ASSERTₘ (#APPLY f n₁)))))
  aw w1 e1 (a1 , a2 , b1 , b2 , a∈ , c₁ , c₂ , b∈) =
    a1 , a2 , a∈ , b1 ,
    →≡equalInType (sub0-ASSERTₘ-APPLY a1 f) (equalInType-refl b∈)


isType-MP-rightₘ-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                      → equalInType i w #NAT!→NAT! f₁ f₂
                      → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                                     → equalTypes i w' (sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                       (sub0 b (#[0]ASSERTₘ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-rightₘ-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERTₘ-APPLY a₁ f₁))
    (sym (sub0-ASSERTₘ-APPLY a₂ f₂))
    (equalInType-NAT!→equalTypes-ASSERTₘ (equalInType-FUN→ (≡CTerm→equalInType #NAT!→NAT!≡ f∈) w1 e1 a₁ a₂ a∈))


→equalInType-#MP-leftₘ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→NAT! f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                            × inhType i w' (#ASSERTₘ (#APPLY f n₁)))))
                                                         → ⊥)
                                         → ⊥)
                          → equalInType i w (#MP-leftₘ f) a₁ a₂
→equalInType-#MP-leftₘ  i w f a₁ a₂ f∈ h =
  equalInType-NEG (eqTypesNEG← (→equalTypes-#MP-rightₘ f∈)) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#MP-rightₘ f)) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                               × inhType i w' (#ASSERTₘ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) =
          equalInType-NEG→ g∈ w2 e2 (#PAIR n₁ t) (#PAIR n₁ t) s∈
          where
            s∈ : equalInType i w2 (#MP-rightₘ f) (#PAIR n₁ t) (#PAIR n₁ t)
            s∈ = equalInType-SUM!
                   (λ w' _ → isTypeNAT!)
                   (isType-MP-rightₘ-body i w2 f f (equalInType-mon f∈ w2 (⊑-trans· e1 e2)))
                   (Mod.∀𝕎-□ M aw3)
              where
              aw3 : ∀𝕎 w2 (λ w' _ → SUMeq! (equalInType i w' #NAT!)
                                           (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                           w' (#PAIR n₁ t) (#PAIR n₁ t))
              aw3 w3 e3 =
                n₁ , n₁ , t , t ,
                equalInType-refl (equalInType-mon n∈ w3 e3) ,
                #⇛!-refl {w3} {#PAIR n₁ t} ,
                #⇛!-refl {w3} {#PAIR n₁ t} ,
                ≡CTerm→equalInType (sym (sub0-ASSERTₘ-APPLY n₁ f)) (equalInType-mon inh w3 e3)


∈#MPₘ→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
       → equalInType i w #MPₘ F G
       → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' #NAT!→NAT! f
                      → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                         × inhType i w' (#ASSERTₘ (#APPLY f n₁)))))
                                                      → ⊥)
                                      → ⊥)
                      → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                        × inhType i w' (#ASSERTₘ (#APPLY f n₁))))))
∈#MPₘ→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-rightₘ→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#NAT!→NAT!} {#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-leftₘ f) a₁ a₂
                        → equalInType i w' (#MP-rightₘ f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mpₘ f) h1)

    h3 : equalInType i w1 (#MP-rightₘ f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-leftₘ i w1 f #AX #AX f∈ cond)


#strongMonEq→NOREADeq : {w : 𝕎·} {a b : CTerm}
                      → #strongMonEq w a b
                      → NOREADeq w a b
#strongMonEq→NOREADeq {w} {a} {b} (n , c₁ , c₂) =
  ca , cb
  where
    ca : #⇓→#⇛ w a
    ca = #⇛val→#⇓→#⇛ {w} {a} {#NUM n} tt c₁

    cb : #⇓→#⇛ w b
    cb = #⇛val→#⇓→#⇛ {w} {b} {#NUM n} tt c₂


eqInType-⇛-NAT-rev : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                     → (eqt : equalTypes u w #NAT #NAT)
                     → □· w (λ w' e → #strongMonEq w' a b)
                     → equalTerms u w eqt a b
eqInType-⇛-NAT-rev u w a b eqt h =
  eqInType-⇛-ISECT-rev
    (uni u) w #NAT #NAT #QNAT #QNAT #NOREAD #NOREAD a b
    (λ w1 e1 → eqTypesQNAT)
    (λ w1 e1 → eqTypesNOREAD)
    (wPredExtIrr-eqInType {u} {w} {#QNAT} {#QNAT} (λ w' _ → eqTypesQNAT))
    (wPredExtIrr-eqInType {u} {w} {#NOREAD} {#NOREAD} (λ w' _ → eqTypesNOREAD))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#QNAT} {#QNAT} eqTypesQNAT)
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#NOREAD} {#NOREAD} eqTypesNOREAD)
    (#⇛-refl w #NAT) (#⇛-refl w #NAT)
    eqt (Mod.∀𝕎-□Func M aw1 h)
  where
    aw1 : ∀𝕎 w (λ w' e' → #strongMonEq w' a b
                        → ISECTeq (eqInType (uni u) w' eqTypesQNAT) (eqInType (uni u) w' eqTypesNOREAD) a b)
    aw1 w1 e1 z1 = Mod.∀𝕎-□ M aw2 , Mod.∀𝕎-□ M λ w2 e2 → #strongMonEq→NOREADeq {w2} {a} {b} (#strongMonEq-mon {a} {b} z1 w2 e2)
      where
      aw2 : ∀𝕎 w1 (λ w' e → QNATeq w' a b)
      aw2 w2 e2 = #strongMonEq→#weakMonEq {w2} {a} {b} (#strongMonEq-mon {a} {b} z1 w2 e2)


#⇛!sameℕ→#strongMonEq : {w : 𝕎·} {a b : CTerm}
                      → #⇛!sameℕ w a b
                      → #strongMonEq w a b
#⇛!sameℕ→#strongMonEq {w} {a} {b} (n , c₁ , c₂) =
  n , #⇛!→#⇛ {w} {a} {#NUM n} c₁ , #⇛!→#⇛ {w} {b} {#NUM n} c₂


#⇛!sameℕ→NOWRITEeq : {w : 𝕎·} {a b : CTerm}
                   → #⇛!sameℕ w a b
                   → NOWRITEeq w a b
#⇛!sameℕ→NOWRITEeq {w} {a} {b} (n , c₁ , c₂) =
  ca , cb
  where
    ca : #⇓→#⇓! w a
    ca = #⇛!-val→#⇓→#⇓! {w} {#NUM n} {a} c₁ tt

    cb : #⇓→#⇓! w b
    cb = #⇛!-val→#⇓→#⇓! {w} {#NUM n} {b} c₂ tt


#⇛!sameℕ-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a b : CTerm}
                 → #⇛!sameℕ w1 a b
                 → #⇛!sameℕ w2 a b
#⇛!sameℕ-mon {w1} {w2} e {a} {b} (n , c₁ , c₂) = n , ∀𝕎-mon e c₁ , ∀𝕎-mon e c₂


eqInType-⇛-NAT!-rev : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                    → (eqt : equalTypes u w #NAT! #NAT!)
                    → □· w (λ w' e → #⇛!sameℕ w' a b)
                    → equalTerms u w eqt a b
eqInType-⇛-NAT!-rev u w a b eqt eqi =
  eqInType-⇛-ISECT-rev
    (uni u) w #NAT! #NAT! #NAT #NAT #NOWRITE #NOWRITE a b
    (λ w1 e1 → eqTypesNAT)
    (λ w1 e1 → eqTypesNOWRITE)
    (wPredExtIrr-eqInType {u} {w} {#NAT} {#NAT} (λ w' _ → eqTypesNAT))
    (wPredExtIrr-eqInType {u} {w} {#NOWRITE} {#NOWRITE} (λ w' _ → eqTypesNOWRITE))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#NAT} {#NAT} eqTypesNAT)
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#NOWRITE} {#NOWRITE} eqTypesNOWRITE)
    (#⇛-refl w #NAT!) (#⇛-refl w #NAT!)
    eqt (Mod.∀𝕎-□Func M aw1 eqi)
  where
    aw1 : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                        → ISECTeq (eqInType (uni u) w' eqTypesNAT) (eqInType (uni u) w' eqTypesNOWRITE) a b)
    aw1 w1 e1 z1 =
      eqInType-⇛-NAT-rev u w1 a b eqTypesNAT (Mod.∀𝕎-□Func M (λ w2 e2 z → #⇛!sameℕ→#strongMonEq {w2} {a} {b} z) (Mod.↑□ M eqi e1)) ,
      Mod.∀𝕎-□ M λ w2 e2 → #⇛!sameℕ→NOWRITEeq {w2} {a} {b} (#⇛!sameℕ-mon e2 {a} {b} z1)


#⇛!→#⇛!sameℕ-rev : {w : 𝕎·} {a b c d : CTerm}
                 → b #⇛! a at w
                 → d #⇛! c at w
                 → #⇛!sameℕ w a c
                 → #⇛!sameℕ w b d
#⇛!→#⇛!sameℕ-rev {w} {a} {b} {c} {d} c1 c2 (n , c₁ , c₂) =
  n , #⇛!-trans {w} {b} {a} {#NUM n} c1 c₁ , #⇛!-trans {w} {d} {c} {#NUM n} c2 c₂


equalTerms-pres-#⇛-left-rev-NAT! : equalTerms-pres-#⇛-left-rev #NAT!
equalTerms-pres-#⇛-left-rev-NAT! {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-NAT!-rev i w a c eqt
    (Mod.∀𝕎-□Func M
      (λ w1 e1 h → #⇛!→#⇛!sameℕ-rev {w1} {b} {a} {c} {c} (∀𝕎-mon e1 comp) (#⇛!-refl {w1} {c}) h)
      (equalInType-NAT!→ i w b c (eqt , eqi)))


→equalInType-CS-NAT!→NAT! : {n : ℕ} {w : 𝕎·} {a b : Name}
                          → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #NAT! (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                          → equalInType n w #NAT!→NAT! (#CS a) (#CS b)
→equalInType-CS-NAT!→NAT! {n} {w} {a} {b} i rewrite #NAT!→NAT!≡ =
  →equalInType-CS-NAT!→T isTypeNAT! equalTerms-pres-#⇛-left-rev-NAT! i


equalInType-#⇛!-type-rev : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                         → T #⇛! U at w
                         → equalInType i w U a b
                         → equalInType i w T a b
equalInType-#⇛!-type-rev {i} {w} {T} {U} {a} {b} comp a∈ =
  TSext-equalTypes-equalInType i w U T a b
    (equalTypes-#⇛-left-right-rev {i} {w} {U} {U} {T} {U} (#⇛-refl w U) (#⇛!→#⇛ {w} {T} {U} comp) (fst a∈))
    a∈


equalInType-#⇛!-type : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                     → T #⇛! U at w
                     → equalInType i w T a b
                     → equalInType i w U a b
equalInType-#⇛!-type {i} {w} {T} {U} {a} {b} comp a∈ =
  TSext-equalTypes-equalInType i w T U a b
    (equalTypes-#⇛-left-right {i} {w} {T} {T} {U} {T} (#⇛!-refl {w} {T}) comp (fst a∈))
    a∈


EQ-N0→NATREC-TRUE : (n : ℕ) (w : 𝕎·) (t u a₁ a₂ b₁ b₂ : CTerm)
                  → equalInType n w (#EQ t #N0 #NAT!) a₁ a₂
                  → equalInType n w (#NATREC t #TRUE u) b₁ b₂
EQ-N0→NATREC-TRUE n w t u a₁ a₂ b₁ b₂ h =
  equalInType-local (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ n w t #N0 (equalInType-EQ→₁ h)))
  where
  aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' t #N0
                     → equalInType n w' (#NATREC t #TRUE u) b₁ b₂)
  aw w1 e1 (k , c₁ , c₂)  rewrite sym (#NUMinj (#⇛!→≡ {#N0} {#NUM k} {w1} c₂ tt)) =
    equalInType-#⇛!-type-rev {n} {w1} {#NATREC t #TRUE u} {#TRUE}
      (#NUM→NATREC⇛! {t} {0} #TRUE u {w1} c₁) (→equalInType-TRUE n)


¬ΣNAT!→¬inhType-Σchoiceₘ-eq : Nat!ℂ CB → (a : CTerm) (name : Name)
                            → sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (CTerm→CTerm0 Cℂ₁) (CTerm→CTerm0 Typeℂ₀₁·))
                            ≡ #EQ (#APPLY (#CS name) a) #N0 #NAT!
¬ΣNAT!→¬inhType-Σchoiceₘ-eq bcb a name
  rewrite snd (snd bcb) | fst bcb
  = CTerm≡ (≡EQ (≡APPLY refl (trans (#shiftDown 0 (ct (shiftUp 0 ⌜ a ⌝) (→#shiftUp 0 {⌜ a ⌝} (CTerm.closed a))))
                                    (#shiftUp 0 a))) refl refl)


¬ΣNAT!→¬inhType-Σchoiceₘ : Nat!ℂ CB → (n : ℕ) (w : 𝕎·) (name : Name)
                         → ∀𝕎 w (λ w' _ → ¬ Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                            × inhType n w' (#ASSERTₘ (#APPLY (#CS name) n₁)))))
                         → ∀𝕎 w (λ w' _ → ¬ inhType n w' (#Σchoice name ℂ₁·))
¬ΣNAT!→¬inhType-Σchoiceₘ bcb n w name aw w1 e1 (t , inh) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
  where
    h0 : ∈Type n w1 (#SUM #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) t
    h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) inh

    h1 : □· w1 (λ w' _ → SUMeq (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' t t)
    h1 = equalInType-SUM→ h0

    aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #NAT!)
                                 (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                 w' t t
                          → Lift (lsuc L) ⊥)
    aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) =
      lift (aw w2 (⊑-trans· e1 e2) (a₁ , a₂ , ea , b₁ , equalInType-refl eqi2))
      where
      eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
      eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

      eqi2 : equalInType n w2 (#ASSERTₘ (#APPLY (#CS name) a₁)) b₁ b₂
      eqi2 = ≡CTerm→equalInType (sym (#ASSERTₘ≡ (#APPLY (#CS name) a₁)))
               (EQ-N0→NATREC-TRUE n w2 (#APPLY (#CS name) a₁) (#LAMBDA (#[0]LAMBDA #[1]FALSE)) b₁ b₂ b₁ b₂
                 (≡CTerm→equalInType (¬ΣNAT!→¬inhType-Σchoiceₘ-eq bcb a₁ name) eb))


#APPLY2-LAMBDA-LAMBDA-FALSE⇛! : (w : 𝕎·) (a b : CTerm)
                              → #APPLY2 (#LAMBDA (#[0]LAMBDA #[1]FALSE)) a b #⇛! #FALSE at w
#APPLY2-LAMBDA-LAMBDA-FALSE⇛! w a b w1 e1 = lift (2 , refl)


inhType-ASSERTₘ→∈NAT! : (i : ℕ) (w : 𝕎·) (t : CTerm)
                      → ∈Type i w #NAT! t
                      → inhType i w (#ASSERTₘ t)
                      → equalInType i w #NAT! t #N0
inhType-ASSERTₘ→∈NAT! i w t t∈ (q , q∈) =
  equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w t t t∈))
  where
  aw1 : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' t t → equalInType i w' #NAT! t #N0)
  aw1 w1 e1 (n , c₁ , c₂) =
    equalInType-#⇛ₚ-left-right-rev {i} {w1} {#NAT!} {t} {#NUM n} {#N0} {#N0}
      c₁ (#⇛!-refl {w1} {#N0}) (concl n q∈2)
    where
    q∈1 : ∈Type i w1 (#NATREC t #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))) q
    q∈1 = ≡CTerm→equalInType (#ASSERTₘ≡ t) (equalInType-mon q∈ w1 e1)

    q∈2 : ∈Type i w1 (#NATRECr n #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))) q
    q∈2 = equalInType-#⇛!-type {i} {w1}
            {#NATREC t #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))}
            {#NATRECr n #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))}
            {q} {q}
            (#NUM→NATREC⇛! {t} {n} #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)) c₁)
            q∈1

    concl : (n : ℕ)
          → ∈Type i w1 (#NATRECr n #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))) q
          → equalInType i w1 #NAT! (#NUM n) #N0
    concl 0 h = NUM-equalInType-NAT! i w1 0
    concl (suc n) h =
      ⊥-elim (¬equalInType-FALSE {w1} {i} {q} {q}
               (equalInType-#⇛!-type {i} {w1}
                  {#NATRECr (suc n) #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))} {#FALSE}
                  {q} {q}
                  (#APPLY2-LAMBDA-LAMBDA-FALSE⇛! w1 (#NUM n) (#NATREC (#NUM n) #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))))
                  h))


#SUM-ASSERTₘ→#Σchoice : Nat!ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                       → compatible· name w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                       → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w #NAT! n₁ n₂
                         × inhType n w (#ASSERTₘ (#APPLY (#CS name) n₁))))
                       → inhType n w (#Σchoice name ℂ₁·)
#SUM-ASSERTₘ→#Σchoice bcb {n} {w} {name} comp sat (n₁ , n₂ , n∈ , inh) =
  #PAIR n₁ #AX ,
  ≡CTerm→equalInType (sym (#Σchoice≡ name ℂ₁·))
    (equalInType-SUM {n} {w} {#NAT!} {#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) (CTerm→CTerm0 Typeℂ₀₁·)}
       (λ w1 e1 → isTypeNAT!)
       aw1
       (Mod.∀𝕎-□ M aw2))
  where
  aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                     → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) (CTerm→CTerm0 Typeℂ₀₁·)))
                                       (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) (CTerm→CTerm0 Typeℂ₀₁·))))
  aw1 w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (¬ΣNAT!→¬inhType-Σchoiceₘ-eq bcb a₁ name))
      (sym (¬ΣNAT!→¬inhType-Σchoiceₘ-eq bcb a₂ name))
      (eqTypesEQ← {w1} {n} {#APPLY (#CS name) a₁} {#N0} {#APPLY (#CS name) a₂} {#N0} {#NAT!} {#NAT!}
        isTypeNAT!
        (≡CTerm→equalInType (proj₁ bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e1 comp) a∈))
        (NUM-equalInType-NAT! n w1 0))

  aw2 : ∀𝕎 w (λ w' _ → SUMeq (equalInType n w' #NAT!)
                             (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) (CTerm→CTerm0 Typeℂ₀₁·))))
                             w' (#PAIR n₁ #AX) (#PAIR n₁ #AX))
  aw2 w1 e1 =
    n₁ , n₁ , #AX , #AX , equalInType-refl (equalInType-mon n∈ w1 e1) ,
    ⇓-refl ⌜ #PAIR n₁ #AX ⌝ w1 , ⇓-refl ⌜ #PAIR n₁ #AX ⌝ w1  ,
    ≡CTerm→equalInType (sym (¬ΣNAT!→¬inhType-Σchoiceₘ-eq bcb n₁ name))
      (→equalInType-EQ {n} {w1} {#APPLY (#CS name) n₁} {#N0} {#NAT!} {#AX} {#AX}
        (inhType-ASSERTₘ→∈NAT! n w1 (#APPLY (#CS name) n₁) h1 (inhType-mon e1 inh)))
    where
    h1 : ∈Type n w1 #NAT! (#APPLY (#CS name) n₁)
    h1 = ≡CTerm→equalInType (proj₁ bcb)
           (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e1 comp) (equalInType-refl (equalInType-mon n∈ w1 e1)))


-- Nat!ℂ CB is for NAT! which works only for FCSs
-- alwaysFreezable is also for FCSs
-- This version uses non-truncated Σs, and noread/nowrite ℕ and 𝔹
¬MPₘ : Nat!ℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MPₘ) #lamAX
¬MPₘ bcb afb w n = equalInType-NEG (isTypeMPₘ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MPₘ a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type n w' #NAT!→NAT! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                                  × inhType n w' (#ASSERTₘ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERTₘ (#APPLY f n₁))))))
        aw2 = ∈#MPₘ→ n w1 F G ea

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

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #NAT! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (proj₁ bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→NAT! f
        eqf1 = →equalInType-CS-NAT!→NAT! eqf2

        h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERTₘ (#APPLY f n₁)))))
                                           → ⊥)
                           → ⊥)
        h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice n w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (afb name w3) z
          where
            z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType n w4 (#Σchoice name ℂ₁·))
            z = ¬ΣNAT!→¬inhType-Σchoiceₘ bcb n w3 name aw

        h4 : □· w2 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                             × inhType n w' (#ASSERTₘ (#APPLY f n₁)))))
        h4 = aw2 w2 e2 f eqf1 h3

        -- We follow the choice
        w3 : 𝕎·
        w3 = fst (followChoice· name h4 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (followChoice· name h4 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
        oc2 = fst (snd (snd (followChoice· name h4 oc1 comp1 fb1)))

        comp2 : compatible· name w3 Resℂ
        comp2 = fst (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

        h6 : Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w3 #NAT! n₁ n₂
              × inhType n w3 (#ASSERTₘ (#APPLY f n₁))))
        h6 = snd (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice name ℂ₁·)
        h7 = #SUM-ASSERTₘ→#Σchoice bcb comp2 (0 , sat-ℂ₁ 0) h6

        h8 : ¬ inhType n w3 (#Σchoice name ℂ₁·)
        h8 = ¬equalInType-#Σchoice n w3 Resℂ name isValueℂ₀· isValueℂ₁· ¬∼ℂ₀₁· oc2 comp2 fb2


-- A variant of Σchoice that uses NAT instead of NAT!
Σchoiceₙ : (n : Name) (k : ℂ·) → Term
Σchoiceₙ n k = SUM NAT (EQ (APPLY (CS n) (VAR 0)) (ℂ→T k) typeℂ₀₁)


#Σchoiceₙ : (n : Name) (k : ℂ·) → CTerm
#Σchoiceₙ n k = ct (Σchoiceₙ n k) c
  where
    c : # (Σchoiceₙ n k)
    c rewrite #-typeℂ₀₁ | #-ℂ→T k = refl


#Σchoiceₙ≡ : (n : Name) (k : ℂ·) → #Σchoiceₙ n k ≡ #SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS n) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)
#Σchoiceₙ≡ n k = CTerm≡ refl


{--
→equalInType-APPLY-CSₙ-Typeℂ₀₁· : {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                                  → compatible· c w Resℂ
                                  → equalInType i w #NAT a₁ a₂
                                  → equalInType i w Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CSₙ-Typeℂ₀₁· {i} {w} {c} {a₁} {a₂} comp eqi =
  equalInType-local (Mod.∀𝕎-□Func M aw1' (equalInType-NAT→ i w a₁ a₂ eqi))
  where
    aw1' : ∀𝕎 w (λ w'' e'' → #strongMonEq w'' a₁ a₂ → equalInType i w'' Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂))
    aw1' w1 e1 (n , c₁ , c₂) = {!!}
{--      equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev
        _ #⇛Typeℂ₀₁-rev·
        (#⇛!-APPLY-CS {w1} {a₁} {#NUM n} c c₁) (#⇛!-APPLY-CS {w1} {a₂} {#NUM n} c c₂) eqj
--}
 -- #⇛Typeℂ₀₁· {!!} {!!} {!!} --equalInType-#⇛-LR-rev (#⇛!-APPLY-CS {w1} {a₁} {#NUM n} c c₁) (#⇛!-APPLY-CS {w1} {a₂} {#NUM n} c c₂) eqj
      where
        j2 : □· w1 (λ w' _ → weakℂ₀₁M w' (getT n c))
        j2 = comp-Resℂ→□·-weakℂ₀₁ n (⊑-compatible· e1 comp)

        eqj : ∈Type i w1 Typeℂ₀₁· (#APPLY (#CS c) (#NUM n))
        eqj = →∈Typeℂ₀₁· i j2


equalTypes-#Σchoiceₙ-body : (i : ℕ) (w : 𝕎·) (c : Name) (k : ℂ·)
                           → compatible· c w Resℂ
                           → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                           → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                           → equalInType i w' #NAT a₁ a₂
                                           → equalTypes i w' (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k) Typeℂ₀₁·)
                                                              (#EQ (#APPLY (#CS c) a₂) (ℂ→C· k) Typeℂ₀₁·))
equalTypes-#Σchoiceₙ-body i w c k comp sat w' e' a₁ a₂ ea =
  eqTypesEQ← (Typeℂ₀₁-isType· i w') aw1 aw2
  where
    aw1 : equalInType i w' Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
    aw1 = {!!} --→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e' comp) ea

    aw2 : equalInType i w' Typeℂ₀₁· (ℂ→C· k) (ℂ→C· k)
    aw2 = sat→equalInType-Typeℂ₀₁· i w' k sat


equalTypes-#Σchoiceₙ-body-sub0 : (i : ℕ) (w : 𝕎·) (c : Name) (k : ℂ·)
                                → compatible· c w Resℂ
                                → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                                → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                                → equalInType i w' #NAT a₁ a₂
                                                → equalTypes i w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁))
                                                                   (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)))
equalTypes-#Σchoiceₙ-body-sub0 i w c k comp sat w' e' a₁ a₂ ea rewrite sub0-#Σchoice-body≡ a₁ c k | sub0-#Σchoice-body≡ a₂ c k =
  {!!} --equalTypes-#Σchoice-body i w c k comp sat w' e' a₁ a₂ ea


#SUM-ASSERTₙ→#Σchoiceₙ : Boolℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                       → compatible· name w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                       → inhType n w (#SUM-ASSERTₙ (#CS name))
                       → inhType n w (#Σchoiceₙ name ℂ₁·)
#SUM-ASSERTₙ→#Σchoiceₙ bcb {n} {w} {name} comp sat (t , inh) =
  {!!}
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

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = {!!} --equalTypes-#Σchoice-body-sub0 n w name ℂ₁· comp sat



¬MPₙ : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MPₙ) #lamAX
¬MPₙ bcb afb w n = equalInType-NEG (isTypeMPₙ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MPₙ a₁ a₂)
    aw1 w1 e1 F G ea = {!!}
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type n w' #NAT→BOOL f
                             → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT n₁ n₂
                                                                    × inhType n w' (#ASSERT₂ (#APPLY f n₁)))))
                                                                → ⊥)
                                              → ⊥)
                             → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT n₁ n₂
                                                 × inhType n w' (#ASSERT₂ (#APPLY f n₁))))))
        aw2 = ∈#MPₙ→ n w1 F G ea
--}


-- This is similar to ¬MP but proved here for #MP₂, which is stated using ¬¬∃, instead of #MP, which is stated using ¬∀¬
¬MP₂ : Bool₀ℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₂) #lamAX
¬MP₂ bcb afb w n =
  →∈Type-NEG n w #MP #MP₂ #lamAX #lamAX (isTypeMP₂ w n) aw1 (¬MP bcb afb w n)
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' #NAT!→BOOL₀ f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp f₁))
        (sym (sub0-fun-mp f₂))
        (eqTypesFUN← (→equalTypes-#MP-left f∈) (→equalTypes-#MP-right f∈))

    p3 : ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type n w' #NAT!→BOOL₀ a
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
        n w1 #NAT!→BOOL₀ #NAT!→BOOL₀
        (#[0]FUN #[0]MP-left3 #[0]MP-right)
        (#[0]FUN #[0]MP-left #[0]MP-right)
        u₁ u₂ (isType-#NAT!→BOOL₀ w1 n) (∀𝕎-mon e1 p2) (λ w1 e1 a b h → h)
        (∀𝕎-mon e1 p3) u∈


-- This is similar to ¬MP₂ but proved here for an non-truncated version of #MP₂
¬MP₃ : Bool₀ℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₃) #lamAX
¬MP₃ bcb afb w n =
  →∈Type-NEG n w #MP₂ #MP₃ #lamAX #lamAX (isTypeMP₃ w n) aw1 (¬MP₂ bcb afb w n)
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' #NAT!→BOOL₀ f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left3 #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left3 #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp₂ f₁))
        (sym (sub0-fun-mp₂ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left3 f∈) (→equalTypes-#MP-right f∈))

    p3 : ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type n w' #NAT!→BOOL₀ a
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
        n w1 #NAT!→BOOL₀ #NAT!→BOOL₀
        (#[0]FUN #[0]MP-left2 #[0]MP-right2)
        (#[0]FUN #[0]MP-left3 #[0]MP-right)
        u₁ u₂ (isType-#NAT!→BOOL₀ w1 n) (∀𝕎-mon e1 p2) (λ w1 e1 a b h → h)
        (∀𝕎-mon e1 p3) u∈

\end{code}[hide]
