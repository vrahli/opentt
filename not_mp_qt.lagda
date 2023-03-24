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


module not_mp_qt {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import not_mp(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)


#QTNAT!→T : CTerm → CTerm
#QTNAT!→T T = #FUN #QTNAT! T


cℂ : Set(lsuc(L))
cℂ = (c : Name) (w : 𝕎·) (n : ℕ)
      → compatible· c w Resℂ
      → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (getChoice· n c w' ≡ just ℂ₀· ⊎ getChoice· n c w' ≡ just ℂ₁·))


-- It seems that this would only be true with references because we don't have to jump to where 'a' is defined at 'n'
-- and we might then be able to use cℂ above
⇓!sameℕ→⇓!same-bool : (cb : QTBoolℂ CB) (cc : cℂ) (w : 𝕎·) (t1 t2 : Term) (a : Name)
                         → compatible· a w Resℂ
                         → ⇓!sameℕ w t1 t2
                         → ⇓!same-bool w (APPLY (CS a) t1) (APPLY (CS a) t2)
⇓!sameℕ→⇓!same-bool cb cc w t1 t2 a compat (n , c₁ , c₂) with lower (cc a w n compat w (⊑-refl· w))
... | inj₁ gc = AX , AX , inj₂ (Σ-steps-APPLY-CS (fst c₁) t1 BFALSE w w n a (snd c₁) gt ,
                                Σ-steps-APPLY-CS (fst c₂) t2 BFALSE w w n a (snd c₂) gt)
    where
      gt : getT n a w ≡ just BFALSE
      gt rewrite gc = ≡just (≡CTerm (fst (snd cb)))
... | inj₂ gc = AX , AX , inj₁ (Σ-steps-APPLY-CS (fst c₁) t1 BTRUE w w n a (snd c₁) gt ,
                                Σ-steps-APPLY-CS (fst c₂) t2 BTRUE w w n a (snd c₂) gt)
    where
      gt : getT n a w ≡ just BTRUE
      gt rewrite gc = ≡just (≡CTerm (snd (snd cb)))


⇓!sameℕ→#⇓!same-bool : (cb : QTBoolℂ CB) (cc : cℂ) (w : 𝕎·) (t1 t2 : CTerm) (a : Name)
                         → compatible· a w Resℂ
                         → ⇓!sameℕ w ⌜ t1 ⌝ ⌜ t2 ⌝
                         → #⇓!same-bool w (#APPLY (#CS a) t1) (#APPLY (#CS a) t2)
⇓!sameℕ→#⇓!same-bool cb cc w t1 t2 a compat (n , c₁ , c₂) with lower (cc a w n compat w (⊑-refl· w))
... | inj₁ gc = #AX , #AX , inj₂ (Σ-steps-APPLY-CS (fst c₁) ⌜ t1 ⌝ BFALSE w w n a (snd c₁) gt ,
                                  Σ-steps-APPLY-CS (fst c₂) ⌜ t2 ⌝ BFALSE w w n a (snd c₂) gt)
    where
      gt : getT n a w ≡ just BFALSE
      gt rewrite gc = ≡just (≡CTerm (fst (snd cb)))
... | inj₂ gc = #AX , #AX , inj₁ (Σ-steps-APPLY-CS (fst c₁) ⌜ t1 ⌝ BTRUE w w n a (snd c₁) gt ,
                                  Σ-steps-APPLY-CS (fst c₂) ⌜ t2 ⌝ BTRUE w w n a (snd c₂) gt)
    where
      gt : getT n a w ≡ just BTRUE
      gt rewrite gc = ≡just (≡CTerm (snd (snd cb)))


→equalInType-CS-QTNAT!→QTBOOL! : (cb : QTBoolℂ CB) (cc : cℂ) {n : ℕ} {w : 𝕎·} {a : Name}
                                   → compatible· a w Resℂ
                                   → ∈Type n w (#QTNAT!→QTBOOL!) (#CS a)
→equalInType-CS-QTNAT!→QTBOOL! cb cc {n} {w} {a} compat =
  equalInType-FUN eqTypesQTNAT! (eqTypesQTBOOL! {w} {n}) aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #QTNAT! a₁ a₂
                      → equalInType n w' #QTBOOL! (#APPLY (#CS a) a₁) (#APPLY (#CS a) a₂))
    aw w1 e1 a₁ a₂ ea =
      →equalInType-QTBOOL! n w1 (#APPLY (#CS a) a₁) (#APPLY (#CS a) a₂) (Mod.∀𝕎-□Func M aw1 ea1)
      where
        ea1 : □· w1 (λ w' _ → #weakMonEq! w' a₁ a₂)
        ea1 = equalInType-QTNAT!→ n w1 a₁ a₂ ea

        aw1 : ∀𝕎 w1 (λ w' e' → #weakMonEq! w' a₁ a₂ → #weakBool! w' (#APPLY (#CS a) a₁) (#APPLY (#CS a) a₂))
        aw1 w2 e2 wm w3 e3 = lift (⇓!sameℕ→#⇓!same-bool cb cc w3 a₁ a₂ a (⊑-compatible· (⊑-trans· e1 (⊑-trans· e2 e3)) compat) (lower (wm w3 e3)))
 {--(m , c₁ , c₂) = equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev
                                    T pres {n} {w2}
                                    {#APPLY (#CS a) a₁} {#APPLY (#CS a) (#NUM m)} {#APPLY (#CS b) a₂} {#APPLY (#CS b) (#NUM m)}
                                    (#⇛!-APPLY-CS {w2} {a₁} {#NUM m} a c₁)
                                    (#⇛!-APPLY-CS {w2} {a₂} {#NUM m} b c₂)
                                    (i w2 (⊑-trans· e1 e2) m)
--}


¬MP₅ : (bcb : QTBoolℂ CB) (cc : cℂ) → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₅) #lamAX
¬MP₅ bcb cc afb w n = equalInType-NEG (isTypeMP₅ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP₅ a₁ a₂)
    aw1 w1 e1 F G ea = {!!} --h8 h7
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type n w' #QTNAT!→QTBOOL! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂
                                                                  × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂
                                              × inhType n w' (#ASSERT₃ (#APPLY f n₁))))))
        aw2 = ∈#MP₅→ n w1 F G ea

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

        --eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #QTBOOL! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        --eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #QTNAT!→QTBOOL! f
        eqf1 = →equalInType-CS-QTNAT!→QTBOOL! bcb cc {n} {w2} {name} comp1 --→equalInType-CS-QTNAT!→QTBOOL! eqf2

{--
        h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂
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
--}

\end{code}
