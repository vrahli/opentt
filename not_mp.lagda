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

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)


alwaysFreezable : Freeze W C K P G N → Set(L)
alwaysFreezable f = (c : Name) (w : 𝕎·) → Freeze.freezable f c w


-- Assuming that our choices are Bools
-- and that choices are always freezable (see where it is used below)
-- Boolℂ CB is for BOOL, which then would be only for FCSs, not references, which change over time
¬MP : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP) #lamAX
¬MP bcb afb w n = equalInType-NEG (isTypeMP w n) aw1
  where
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


¬ΣNAT!→¬inhType-Σchoice : QTBoolℂ CB → (n : ℕ) (w : 𝕎·) (name : Name)
                           → ∀𝕎 w (λ w' _ → ¬ Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₃ (#APPLY (#CS name) n₁)))))
                           → ∀𝕎 w (λ w' _ → ¬ inhType n w' (#Σchoice name ℂ₁·))
¬ΣNAT!→¬inhType-Σchoice bcb n w name aw w1 e1 (t , inh) =
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
                                        → ∈Type n w #NAT!→QTBOOL! f
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
      #⇛-refl w1 (#PAIR n₁ t) , #⇛-refl w1 (#PAIR n₁ t) ,
      →≡equalInType (sym (sub0-ASSERT₃-APPLY n₁ f)) (equalInType-mon inh w1 e1)


-- QTBoolℂ CB is for QTBOOL,! which works for FCSs and refs
¬MP₄ : QTBoolℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₄) #lamAX
¬MP₄ bcb afb w n = equalInType-NEG (isTypeMP₄ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP₄ a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type n w' #NAT!→QTBOOL! f
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

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #QTBOOL! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→QTBOOL! f
        eqf1 = →equalInType-CS-NAT!→QTBOOL! eqf2

        h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                                   × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
                                               → ⊥)
                             → ⊥)
        h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice n w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (afb name w3) z
          where
            z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType n w4 (#Σchoice name ℂ₁·))
            z = ¬ΣNAT!→¬inhType-Σchoice bcb n w3 name aw

        h4 : □· w2 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂
                                              × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
        h4 = aw2 w2 e2 f eqf1 h3

        -- We follow the choice
        w3 : 𝕎·
        w3 = fst (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
        oc2 = fst (snd (snd (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1)))

        comp2 : compatible· name w3 Resℂ
        comp2 = fst (snd (snd (snd (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1)))))

        h6 : Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w3 #NAT! n₁ n₂
              × inhType n w3 (#ASSERT₃ (#APPLY f n₁))))
        h6 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice name ℂ₁·)
        h7 = #SUM-ASSERT₃→#Σchoice bcb comp2 (0 , sat-ℂ₁ 0) (ΣinhType-ASSERT₃→inhType-SUM-ASSERT₃ n w3 f (equalInType-mon eqf1 w3 e3) h6)

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
¬MP₂ : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₂) #lamAX
¬MP₂ bcb afb w n =
  →∈Type-NEG n w #MP #MP₂ #lamAX #lamAX (isTypeMP₂ w n) aw1 (¬MP bcb afb w n)
  where
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
¬MP₃ : Boolℂ CB → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₃) #lamAX
¬MP₃ bcb afb w n =
  →∈Type-NEG n w #MP₂ #MP₃ #lamAX #lamAX (isTypeMP₃ w n) aw1 (¬MP₂ bcb afb w n)
  where
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
