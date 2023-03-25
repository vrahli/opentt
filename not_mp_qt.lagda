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
cℂ = (c : Name) (r : Res) (w : 𝕎·) (n : ℕ)
      → compatible· c w r
      → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (getChoice· n c w' ≡ just ℂ₀· ⊎ getChoice· n c w' ≡ just ℂ₁·))


-- It seems that this would only be true with references because we don't have to jump to where 'a' is defined at 'n'
-- and can then use cℂ above
⇓!sameℕ→⇓!same-bool : (cb : QTBoolℂ CB) (cc : cℂ) (w : 𝕎·) (t1 t2 : Term) (a : Name)
                         → compatible· a w Resℂ
                         → ⇓!sameℕ w t1 t2
                         → ⇓!same-bool w (APPLY (CS a) t1) (APPLY (CS a) t2)
⇓!sameℕ→⇓!same-bool cb cc w t1 t2 a compat (n , c₁ , c₂) with lower (cc a Resℂ w n compat w (⊑-refl· w))
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
⇓!sameℕ→#⇓!same-bool cb cc w t1 t2 a compat (n , c₁ , c₂) with lower (cc a Resℂ w n compat w (⊑-refl· w))
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


→equalInType-APPLY-CS-Typeℂ₀₁-qt : (cb : QTBoolℂ CB) (cc : cℂ) {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                                  → compatible· c w Resℂ
                                  → equalInType i w #QTNAT! a₁ a₂
                                  → equalInType i w Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-Typeℂ₀₁-qt cb cc {i} {w} {c} {a₁} {a₂} compat ea =
  ≡CTerm→equalInType
    (sym (fst cb))
    (→equalInType-QTBOOL! i w (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂) (Mod.∀𝕎-□Func M aw1 ea1))
  where
    ea1 : □· w (λ w' _ → #weakMonEq! w' a₁ a₂)
    ea1 = equalInType-QTNAT!→ i w a₁ a₂ ea

    aw1 : ∀𝕎 w (λ w' e' → #weakMonEq! w' a₁ a₂ → #weakBool! w' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂))
    aw1 w1 e1 wm w2 e2 = lift (⇓!sameℕ→#⇓!same-bool cb cc w2 a₁ a₂ c (⊑-compatible· (⊑-trans· e1 e2) compat) (lower (wm w2 e2)))


→equalInType-APPLY-CS-QTBOOL!-qt : (cb : QTBoolℂ CB) (cc : cℂ) {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                                  → compatible· c w Resℂ
                                  → equalInType i w #QTNAT! a₁ a₂
                                  → equalInType i w #QTBOOL! (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-QTBOOL!-qt cb cc {i} {w} {c} {a₁} {a₂} compat ea =
  ≡CTerm→equalInType (fst cb) (→equalInType-APPLY-CS-Typeℂ₀₁-qt cb cc compat ea)


→equalInType-CS-QTNAT!→QTBOOL! : (cb : QTBoolℂ CB) (cc : cℂ) {n : ℕ} {w : 𝕎·} {a : Name}
                                   → compatible· a w Resℂ
                                   → ∈Type n w (#QTNAT!→QTBOOL!) (#CS a)
→equalInType-CS-QTNAT!→QTBOOL! cb cc {n} {w} {a} compat =
  equalInType-FUN eqTypesQTNAT! (eqTypesQTBOOL! {w} {n}) aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #QTNAT! a₁ a₂
                      → equalInType n w' #QTBOOL! (#APPLY (#CS a) a₁) (#APPLY (#CS a) a₂))
    aw w1 e1 a₁ a₂ ea = →equalInType-APPLY-CS-QTBOOL!-qt cb cc (⊑-compatible· e1 compat) ea


Σchoice-qt : (n : Name) (k : ℂ·) → Term
Σchoice-qt n k = SUM QTNAT! (EQ (APPLY (CS n) (VAR 0)) (ℂ→T k) typeℂ₀₁)


#Σchoice-qt : (n : Name) (k : ℂ·) → CTerm
#Σchoice-qt n k = ct (Σchoice-qt n k) c
  where
    c : # (Σchoice-qt n k)
    c rewrite #-typeℂ₀₁ | #-ℂ→T k = refl


#Σchoice-qt≡ : (n : Name) (k : ℂ·) → #Σchoice-qt n k ≡ #SUM #QTNAT! (#[0]EQ (#[0]APPLY (#[0]CS n) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)
#Σchoice-qt≡ n k = CTerm≡ refl


equalTypes-#Σchoice-qt-body : (cb : QTBoolℂ CB) (cc : cℂ) (i : ℕ) (w : 𝕎·) (c : Name) (k : ℂ·)
                           → compatible· c w Resℂ
                           → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                           → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                           → equalInType i w' #QTNAT! a₁ a₂
                                           → equalTypes i w' (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k) Typeℂ₀₁·)
                                                              (#EQ (#APPLY (#CS c) a₂) (ℂ→C· k) Typeℂ₀₁·))
equalTypes-#Σchoice-qt-body cb cc i w c k comp sat w' e' a₁ a₂ ea =
  eqTypesEQ← (Typeℂ₀₁-isType· i w') aw1 aw2
  where
    aw1 : equalInType i w' Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
    aw1 = →equalInType-APPLY-CS-Typeℂ₀₁-qt cb cc (⊑-compatible· e' comp) ea --

    aw2 : equalInType i w' Typeℂ₀₁· (ℂ→C· k) (ℂ→C· k)
    aw2 = sat→equalInType-Typeℂ₀₁· i w' k sat


equalTypes-#Σchoice-qt-body-sub0 : (cb : QTBoolℂ CB) (cc : cℂ) (i : ℕ) (w : 𝕎·) (c : Name) (k : ℂ·)
                                → compatible· c w Resℂ
                                → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                                → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                                → equalInType i w' #QTNAT! a₁ a₂
                                                → equalTypes i w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁))
                                                                   (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)))
equalTypes-#Σchoice-qt-body-sub0 cb cc i w c k comp sat w' e' a₁ a₂ ea rewrite sub0-#Σchoice-body≡ a₁ c k | sub0-#Σchoice-body≡ a₂ c k =
  equalTypes-#Σchoice-qt-body cb cc i w c k comp sat w' e' a₁ a₂ ea


getChoice→equalInType-#Σchoice-qt-aux : (cb : QTBoolℂ CB) (cc : cℂ) {n : ℕ} {name : Name} {w : 𝕎·} {k : ℂ·} (i : ℕ)
                                      → compatible· name w Resℂ
                                      → ·ᵣ Resℂ n k
                                      → #APPLY (#CS name) (#NUM n) #⇛! ℂ→C· k at w
                                      → equalInType
                                           i w
                                           (#SUM #QTNAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁))
                                           (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
getChoice→equalInType-#Σchoice-qt-aux cb cc {n} {name} {w} {k} i comp sat g =
  equalInType-SUM
    {i} {w} {#QTNAT!} {#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁}
    (eqTypes-mon (uni i) eqTypesQTNAT!)
    (equalTypes-#Σchoice-qt-body-sub0 cb cc i w name k comp (0 , sat))
    j
  where
    j : □· w (λ w' _ → SUMeq (equalInType i w' #QTNAT!)
                              (λ a b ea → equalInType i w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)))
                              w'
                              (#PAIR (#NUM n) #AX)
                              (#PAIR (#NUM n) #AX))
    j = Mod.∀𝕎-□ M (λ w1 e1 → #NUM n , #NUM n , #AX , #AX ,
                                NUM-equalInType-QTNAT! i w1 n ,
                                #compAllRefl (#PAIR (#NUM n) #AX) w1 ,
                                #compAllRefl (#PAIR (#NUM n) #AX) w1 ,
                                getChoice→equalInType-#Σchoice-aux1 i sat (∀𝕎-mon e1 g))


getChoice→equalInType-#Σchoice-qt : (cb : QTBoolℂ CB) (cc : cℂ) {n : ℕ} {name : Name} {w : 𝕎·} {k : ℂ·} (i : ℕ)
                                  → compatible· name w Resℂ
                                  → ·ᵣ Resℂ n k
                                  → #APPLY (#CS name) (#NUM n) #⇛! ℂ→C· k at w
                                  → equalInType i w (#Σchoice-qt name k) (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
getChoice→equalInType-#Σchoice-qt cb cc {n} {name} {w} {k} i comp sat g rewrite #Σchoice-qt≡ name k =
  getChoice→equalInType-#Σchoice-qt-aux cb cc i comp sat g


¬∀𝕎¬equalInType-#Σchoice-qt : (cb : QTBoolℂ CB) (cc : cℂ) (i : ℕ) (w : 𝕎·) (name : Name) (k : ℂ·)
                            → ⋆ᵣ Resℂ k
                            → compatible· name w Resℂ
                            → freezable· name w
                            → ¬ ∀𝕎 w (λ w' _ → ¬ inhType i w' (#Σchoice-qt name k))
¬∀𝕎¬equalInType-#Σchoice-qt cb cc i w name k rk comp fb aw = aw w1 e1 (#PAIR (#NUM n1) #AX , h1)
  where
    w1 : 𝕎·
    w1 = freeze· name w k

    e1 : w ⊑· w1
    e1 = freeze⊑· name w k comp rk

    n1 : ℕ
    n1 = fst (getFreeze· name w k comp tt fb)

    g0 : ∀𝕎 w1 (λ w' _ → Lift (lsuc(L)) (getChoice· n1 name w' ≡ just k))
    g0 = snd (getFreeze· name w k comp tt fb)

    g1 : #APPLY (#CS name) (#NUM n1) #⇛! ℂ→C· k at w1
    g1 = →#APPLY-#CS#⇛ℂ→C· g0

    h1 : equalInType i w1 (#Σchoice-qt name k) (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX)
    h1 = getChoice→equalInType-#Σchoice-qt cb cc i (⊑-compatible· e1 comp) (rk 0) g1


¬ΣQTNAT!→¬inhType-Σchoice-qt : QTBoolℂ CB → (n : ℕ) (w : 𝕎·) (name : Name)
                           → ∀𝕎 w (λ w' _ → ¬ Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂ × inhType n w' (#ASSERT₃ (#APPLY (#CS name) n₁)))))
                           → ∀𝕎 w (λ w' _ → ¬ inhType n w' (#Σchoice-qt name ℂ₁·))
¬ΣQTNAT!→¬inhType-Σchoice-qt bcb n w name aw w1 e1 (t , inh) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
  where
    h0 : ∈Type n w1 (#SUM #QTNAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) t
    h0 = ≡CTerm→equalInType (#Σchoice-qt≡ name ℂ₁·) inh

    h1 : □· w1 (λ w' _ → SUMeq (equalInType n w' #QTNAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' t t)
    h1 = equalInType-SUM→ h0

    aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType n w' #QTNAT!)
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


fun-equalInType-SUM-QTNAT! : {n : ℕ} {w : 𝕎·} {a b : CTerm0} {u v : CTerm}
                          → ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #QTNAT! m
                                          → equalInType n w' (sub0 m a) t₁ t₂
                                          → equalInType n w' (sub0 m b) t₁ t₂)
                          → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #QTNAT! a₁ a₂) → equalTypes n w' (sub0 a₁ b) (sub0 a₂ b))
                          → equalInType n w (#SUM #QTNAT! a) u v
                          → equalInType n w (#SUM #QTNAT! b) u v
fun-equalInType-SUM-QTNAT! {n} {w} {a} {b} {u} {v} imp eqb eqi =
  equalInType-SUM
    (λ w' _ → eqTypesQTNAT!)
    eqb
    (Mod.∀𝕎-□Func M aw (equalInType-SUM→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType n w' #QTNAT!) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ a)) w' u v
                        → SUMeq (equalInType n w' #QTNAT!) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ b)) w' u v)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , imp w1 e1 a₁ b₁ b₂ (equalInType-refl ea) eb


#SUM-ASSERT₄→#Σchoice-qt : (bcb : QTBoolℂ CB) (cc : cℂ) → {n : ℕ} {w : 𝕎·} {name : Name}
                       → compatible· name w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                       → inhType n w (#SUM-ASSERT₄ (#CS name))
                       → inhType n w (#Σchoice-qt name ℂ₁·)
#SUM-ASSERT₄→#Σchoice-qt bcb cc {n} {w} {name} comp sat (t , inh) =
  t , ≡CTerm→equalInType
        (sym (#Σchoice-qt≡ name ℂ₁·))
        (fun-equalInType-SUM-QTNAT! {n} {w} {#[0]ASSERT₃ (#[0]APPLY (#[0]CS name) #[0]VAR)} aw1 aw2 inh)
  where
    aw1 : ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #QTNAT! m
                        → equalInType n w' (sub0 m (#[0]ASSERT₃ (#[0]APPLY (#[0]CS name) #[0]VAR))) t₁ t₂
                        → equalInType n w' (sub0 m (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)) t₁ t₂)
    aw1 w1 e1 m t₁ t₂ j eqi = ≡CTerm→equalInType (sym (sub0-#Σchoice-body≡ m name ℂ₁·)) eqi2
      where
        eqi1 : equalInType n w1 (#ASSERT₃ (#APPLY (#CS name) m)) t₁ t₂
        eqi1 = ≡CTerm→equalInType (sub0-ASSERT₃-APPLY m (#CS name)) eqi

        eqt : equalTypes n w1 (#EQ (#APPLY (#CS name) m) #BTRUE #QTBOOL!) (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·)
        eqt = eqTypesEQ← (equalTypes-QTBOOL!-Typeℂ₀₁ bcb n w1)
                          (→equalInType-APPLY-CS-QTBOOL!-qt bcb cc (⊑-compatible· e1 comp) j)
                          (equalInType-QT-BTRUE-ℂ₁ bcb n w1)

        eqi2 : equalInType n w1 (#EQ (#APPLY (#CS name) m) Cℂ₁ Typeℂ₀₁·) t₁ t₂
        eqi2 = equalTypes→equalInType
                 (≡CTerm→eqTypes (sym (#ASSERT₃≡ (#APPLY (#CS name) m))) refl eqt)
                 eqi1

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #QTNAT! a₁ a₂)
                        → equalTypes n w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁))
                                           (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 ℂ₁·) #[0]Typeℂ₀₁)))
    aw2 = equalTypes-#Σchoice-qt-body-sub0 bcb cc n w name ℂ₁· comp sat


ΣinhType-ASSERT₃→inhType-SUM-ASSERT₄ : (n : ℕ) (w : 𝕎·) (f : CTerm)
                                        → ∈Type n w #QTNAT!→QTBOOL! f
                                        → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w #QTNAT! n₁ n₂
                                            × inhType n w (#ASSERT₃ (#APPLY f n₁))))
                                        → inhType n w (#SUM-ASSERT₄ f)
ΣinhType-ASSERT₃→inhType-SUM-ASSERT₄ n w f f∈ (n₁ , n₂ , n∈ , (t , inh)) =
  #PAIR n₁ t ,
  equalInType-SUM
    (λ w' _ → eqTypesQTNAT!)
    (isType-MP-right-qt₂-body n w f f f∈)
    (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType n w' #QTNAT!)
                                (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                w' (#PAIR n₁ t) (#PAIR n₁ t))
    aw w1 e1 =
      n₁ , n₁ , t , t , equalInType-refl (equalInType-mon n∈ w1 e1) ,
      #⇛-refl w1 (#PAIR n₁ t) , #⇛-refl w1 (#PAIR n₁ t) ,
      →≡equalInType (sym (sub0-ASSERT₃-APPLY n₁ f)) (equalInType-mon inh w1 e1)


¬onlyℂ∈𝕎-#weakMonEq!-#weakℂEq : (cc : cℂ) (w : 𝕎·) (c : Name) (r : Res) (a₁ a₂ : CTerm) (k1 : ℂ·)
      → ((w : 𝕎·) → ¬ ∼C! w (ℂ→C· (Res.def r)) (ℂ→C· k1))
      → compatible· c w r
      → onlyℂ∈𝕎 (Res.def r) c w
      → #weakMonEq! w a₁ a₂
      → #weakℂEq w (#APPLY (#CS c) a₁) (ℂ→C· k1)
      → ⊥
¬onlyℂ∈𝕎-#weakMonEq!-#weakℂEq cc w c r a₁ a₂ k1 diff compat only wn wc with lower (wn w (⊑-refl· w))
... | k , c₁ , c₂ with lower (cc c r w k compat w (⊑-refl· w))
... |    inj₁ gc = diff w h3
  where
    h1 : ℂ₀· ≡ Res.def r
    h1 = only k ℂ₀· gc

    gt : getT k c w ≡ just (ℂ→T ℂ₀·)
    gt rewrite gc = refl

    ca : #APPLY (#CS c) a₁ #⇓! ℂ→C· ℂ₀· at w
    ca = Σ-steps-APPLY-CS (fst c₁) ⌜ a₁ ⌝ (ℂ→T ℂ₀·) w w k c (snd c₁) gt

    h2 : ∼C! w (ℂ→C· ℂ₀·) (ℂ→C· k1)
    h2 = lower (wc w (⊑-refl· w)) ℂ₀· k1 ca (⇓!-refl (ℂ→T k1) w)

    h3 : ∼C! w (ℂ→C· (Res.def r)) (ℂ→C· k1)
    h3 = subst (λ x → ∼C! w (ℂ→C· x) (ℂ→C· k1)) h1 h2
... |    inj₂ gc = diff w h3
  where
    h1 : ℂ₁· ≡ Res.def r
    h1 = only k ℂ₁· gc

    gt : getT k c w ≡ just (ℂ→T ℂ₁·)
    gt rewrite gc = refl

    ca : #APPLY (#CS c) a₁ #⇓! ℂ→C· ℂ₁· at w
    ca = Σ-steps-APPLY-CS (fst c₁) ⌜ a₁ ⌝ (ℂ→T ℂ₁·) w w k c (snd c₁) gt

    h2 : ∼C! w (ℂ→C· ℂ₁·) (ℂ→C· k1)
    h2 = lower (wc w (⊑-refl· w)) ℂ₁· k1 ca (⇓!-refl (ℂ→T k1) w)

    h3 : ∼C! w (ℂ→C· (Res.def r)) (ℂ→C· k1)
    h3 = subst (λ x → ∼C! w (ℂ→C· x) (ℂ→C· k1)) h1 h2


¬equalInType-#Σchoice-qt : (cc : cℂ) (i : ℕ) (w : 𝕎·) (r : Res) (c : Name) {k1 : ℂ·}
                        → isValue (ℂ→T (Res.def r))
                        → isValue (ℂ→T k1)
                        → ((w : 𝕎·) → ¬ ∼C! w (ℂ→C· (Res.def r)) (ℂ→C· k1))
                        → onlyℂ∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → ¬ inhType i w (#Σchoice-qt c k1)
¬equalInType-#Σchoice-qt cc i w r c {k1} isv₁ isv₂ diff oc comp fb (x , eqi) =
  ¬onlyℂ∈𝕎-#weakMonEq!-#weakℂEq cc w3 c r a₁ a₂ k1 diff comp3 oc3 (∀𝕎-mon e3 ea3) eb6 --diff w4 sim3
  where
    h0 : equalInType i w (#SUM #QTNAT! (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k1) #[0]Typeℂ₀₁)) x x
    h0 rewrite #Σchoice-qt≡ c k1 = eqi

    h1 : □· w (λ w' _ → SUMeq (equalInType i w' #QTNAT!) (λ a b ea → equalInType i w' (#EQ (#APPLY (#CS c) a) (ℂ→C· k1) Typeℂ₀₁·)) w' x x)
    h1 = Mod.∀𝕎-□Func M aw (equalInType-SUM→ {i} {w} {#QTNAT!} {#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k1) #[0]Typeℂ₀₁} h0)
      where
        aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType i w' #QTNAT!)
                                     (λ a b ea → equalInType i w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k1) #[0]Typeℂ₀₁)))
                                     w' x x
                           → SUMeq (equalInType i w' #QTNAT!)
                                    (λ a b ea → equalInType i w' (#EQ (#APPLY (#CS c) a) (ℂ→C· k1) Typeℂ₀₁·))
                                    w' x x)
        aw w' e' (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) rewrite sub0-#Σchoice-body≡ a₁ c k1 = a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb

    -- 1st jump to bar
    w1 : 𝕎·
    w1 = fst (ChoiceBar.followChoice CB c h1 oc comp fb)

    e1 : w ⊑· w1
    e1 = fst (snd (ChoiceBar.followChoice CB c h1 oc comp fb))

    oc1 : onlyℂ∈𝕎 (Res.def r) c w1
    oc1 = fst (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb)))

    comp1 : compatible· c w1 r
    comp1 = fst (snd (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb))))

    fb1 : freezable· c w1
    fb1 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb)))))

    h2 : SUMeq (equalInType i w1 #QTNAT!) (λ a b ea → equalInType i w1 (#EQ (#APPLY (#CS c) a) (ℂ→C· k1) Typeℂ₀₁·)) w1 x x
    h2 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb)))))

    a₁ : CTerm
    a₁ = fst h2

    a₂ : CTerm
    a₂ = fst (snd h2)

    b₁ : CTerm
    b₁ = fst (snd (snd h2))

    b₂ : CTerm
    b₂ = fst (snd (snd (snd h2)))

    ea1 : equalInType i w1 #QTNAT! a₁ a₂
    ea1 = fst (snd (snd (snd (snd h2))))

    eb1 : equalInType i w1 (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k1) Typeℂ₀₁·) b₁ b₂
    eb1 = snd (snd (snd (snd (snd (snd (snd h2))))))

    -- 2nd jump to bar
    ea2 : □· w1 (λ w' _ → #weakMonEq! w' a₁ a₂)
    ea2 = equalInType-QTNAT!→ i w1 a₁ a₂ ea1

    w2 : 𝕎·
    w2 = fst (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1))

    oc2 : onlyℂ∈𝕎 (Res.def r) c w2
    oc2 = fst (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)))

    comp2 : compatible· c w2 r
    comp2 = fst (snd (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1))))

    fb2 : freezable· c w2
    fb2 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)))))

    ea3 : #weakMonEq! w2 a₁ a₂
    ea3 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)))))

    eb2 : equalInType i w2 (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k1) Typeℂ₀₁·) b₁ b₂
    eb2 = equalInType-mon eb1 w2 e2

    eb3 : equalInType i w2 Typeℂ₀₁· (#APPLY (#CS c) a₁) (ℂ→C· k1)
    eb3 = equalInType-EQ→₁ eb2

    --

    eb5 : □· w2 (λ w' _ → #weakℂEq w' (#APPLY (#CS c) a₁) (ℂ→C· k1))
    eb5 = ∈Typeℂ₀₁→· i w2 (#APPLY (#CS c) a₁) (ℂ→C· k1) eb3

    -- 3rd jump to bar
    w3 : 𝕎·
    w3 = fst (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)

    e3 : w2 ⊑· w3
    e3 = fst (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2))

    oc3 : onlyℂ∈𝕎 (Res.def r) c w3
    oc3 = fst (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)))

    comp3 : compatible· c w3 r
    comp3 = fst (snd (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2))))

    fb3 : freezable· c w3
    fb3 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)))))

    eb6 : #weakℂEq w3 (#APPLY (#CS c) a₁) (ℂ→C· k1)
    eb6 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)))))


-- This version makes use of #QTNAT! and #QTBOOL!
-- It requires alwaysFreezable, which means that all names are always mutable.
-- Freezable/mutable is used to guarantee that if a name is freezable then freezing it will make it immutable.
-- + FCSs are always freezable, because freezable returns always true because FCS slots are immutable once filled out.
-- + References are not always freezable. Freezable retuns whether the cell is frozen, and once it is, it is not freezable anymore.
--   This is because a reference has only 1 cell to fill out.
-- Questions:
-- (1) Is cℂ necessary?
-- (2) Are there stateful computations that satisfy both properties?
¬MP₅ : (bcb : QTBoolℂ CB) (cc : cℂ) → alwaysFreezable F → (w : 𝕎·) (n : ℕ) → ∈Type n w (#NEG #MP₅) #lamAX
¬MP₅ bcb cc afb w n = equalInType-NEG (isTypeMP₅ w n) aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #MP₅ a₁ a₂)
    aw1 w1 e1 F G ea = h8 h7
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

        eqf1 : ∈Type n w2 #QTNAT!→QTBOOL! f
        eqf1 = →equalInType-CS-QTNAT!→QTBOOL! bcb cc {n} {w2} {name} comp1

        h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂
                                                   × inhType n w' (#ASSERT₃ (#APPLY f n₁)))))
                                               → ⊥)
                             → ⊥)
        h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice-qt bcb cc n w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (afb name w3) z
          where
            z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType n w4 (#Σchoice-qt name ℂ₁·))
            z = ¬ΣQTNAT!→¬inhType-Σchoice-qt bcb n w3 name aw

        h4 : □· w2 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂
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

        h6 : Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w3 #QTNAT! n₁ n₂
              × inhType n w3 (#ASSERT₃ (#APPLY f n₁))))
        h6 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB name h4 oc1 comp1 fb1)))))

        h7 : inhType n w3 (#Σchoice-qt name ℂ₁·)
        h7 = #SUM-ASSERT₄→#Σchoice-qt bcb cc comp2 (0 , sat-ℂ₁ 0) (ΣinhType-ASSERT₃→inhType-SUM-ASSERT₄ n w3 f (equalInType-mon eqf1 w3 e3) h6)

        h8 : ¬ inhType n w3 (#Σchoice-qt name ℂ₁·)
        h8 = ¬equalInType-#Σchoice-qt cc n w3 Resℂ name isValueℂ₀· isValueℂ₁· ¬∼ℂ₀₁· oc2 comp2 fb2

\end{code}
