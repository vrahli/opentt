\begin{code}
{-# OPTIONS --rewriting #-}
--{-# OPTIONS --auto-inline #-}

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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
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
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
open import choiceBar


module continuity5b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)



upto𝕎→upto𝕎getT : {name : Name} {w1 w2 : 𝕎·}
                     → upto𝕎 name w1 w2
                     → upto𝕎getT name w1 w2
upto𝕎→upto𝕎getT {name} {w1} {w2} upw = upto𝕎.upwGet upw


upto𝕎→≡dom𝕎 : {name : Name} {w1 w2 : 𝕎·}
                 → upto𝕎 name w1 w2
                 → dom𝕎· w1 ≡ dom𝕎· w2
upto𝕎→≡dom𝕎 {name} {w1} {w2} upw = upto𝕎.upwDom upw


upto𝕎→≡names𝕎 : {name : Name} {w1 w2 : 𝕎·}
                 → upto𝕎 name w1 w2
                 → names𝕎· w1 ≡ names𝕎· w2
upto𝕎→≡names𝕎 {name} {w1} {w2} upw = upto𝕎.upwNames upw


getT≡→map-getT≡ : {n : ℕ} {name name' : Name} {w w' : 𝕎·} {t : Term}
                   → ¬ name' ≡ name
                   → upto𝕎 name w w'
                   → getT n name' w ≡ just t
                   → Data.Maybe.map (λ t → t , w') (getT n name' w') ≡ just (t , w')
getT≡→map-getT≡ {n} {name} {name'} {w} {w'} {t} neq upw gt
  rewrite sym (upto𝕎→upto𝕎getT upw name' n neq) | gt = refl



≡N→≡freshName : {a b : List Name}
                 → a ≡N b
                 → fst (freshName a) ≡ fst (freshName b)
≡N→≡freshName {a} {b} e = ≡N→≡freshNameAux e


→≡++ : {a b c d : List Name} → a ≡ b → c ≡ d → (a ++ c) ≡ (b ++ d)
→≡++ {a} {b} {c} {d} e f rewrite e | f = refl


→≡N++ : {a b c d : List Name} → a ≡N b → c ≡N d → (a ++ c) ≡N (b ++ d)
→≡N++ {a} {b} {c} {d} e f x =
  h1 , h2
  where
    h1 : x ∈ a ++ c → x ∈ b ++ d
    h1 i with ∈-++⁻ a i
    ... | inj₁ p = ∈-++⁺ˡ (fst (e x) p)
    ... | inj₂ p = ∈-++⁺ʳ b (fst (f x) p)

    h2 : x ∈ b ++ d → x ∈ a ++ c
    h2 i with ∈-++⁻ b i
    ... | inj₁ p = ∈-++⁺ˡ (snd (e x) p)
    ... | inj₂ p = ∈-++⁺ʳ a (snd (f x) p)


upto𝕎→≡newChoiceT : {name : Name} {w1 w2 : 𝕎·} (a : Term)
                       → upto𝕎 name w1 w2
                       → newChoiceT w1 a ≡ newChoiceT w2 a
upto𝕎→≡newChoiceT {name} {w1} {w2} a upw =
  ≡N→≡freshName
    {dom𝕎· w1 ++ names𝕎· w1 ++ ↓vars (names a)}
    {dom𝕎· w2 ++ names𝕎· w2 ++ ↓vars (names a)}
    (≡→≡N (→≡++ (upto𝕎.upwDom upw)
                  (→≡++ (upto𝕎.upwNames upw) refl)))


upto𝕎→≡newChoiceT+ : {name : Name} {w1 w2 : 𝕎·} (a : Term)
                       → upto𝕎 name w1 w2
                       → newChoiceT+ w1 a ≡ newChoiceT+ w2 a
upto𝕎→≡newChoiceT+ {name} {w1} {w2} a upw
  rewrite upto𝕎→≡newChoiceT a upw = refl



-- MOVE to computation
fresh-inst : (w : 𝕎·) (a : Term) → Term
fresh-inst w a = shiftNameDown 0 (renn 0 (newChoiceT+ w a) a)


upto𝕎→≡fresh-inst : {name : Name} {w1 w2 : 𝕎·} (a : Term)
                      → upto𝕎 name w1 w2
                      → fresh-inst w1 a ≡ fresh-inst w2 a
upto𝕎→≡fresh-inst {name} {w1} {w2} a upw rewrite upto𝕎→≡newChoiceT+ a upw = refl


-- MOVE to continuity-conds
→≡Nnames𝕎-start : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·)
                   → names𝕎· w1 ≡N names𝕎· w2
                   → names𝕎· (startChoice· name Res⊤ w1) ≡N names𝕎· (startChoice· name Res⊤ w2)
→≡Nnames𝕎-start cc name w1 w2 e
  rewrite ContConds.ccN≡start cc name w1
        | ContConds.ccN≡start cc name w2 = e


-- MOVE to continuity-conds
→≡names𝕎-start : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·)
                   → names𝕎· w1 ≡ names𝕎· w2
                   → names𝕎· (startChoice· name Res⊤ w1) ≡ names𝕎· (startChoice· name Res⊤ w2)
→≡names𝕎-start cc name w1 w2 e
  rewrite ContConds.ccN≡start cc name w1
        | ContConds.ccN≡start cc name w2 = e



-- MOVE to continuity-conds
→dom𝕎-chooseT≡ : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (t : Term)
                   → dom𝕎· w1 ≡ dom𝕎· w2
                   → dom𝕎· (chooseT name w1 t) ≡ dom𝕎· (chooseT name w2 t)
→dom𝕎-chooseT≡ cc name w1 w2 t e =
  trans (ContConds.ccDchoose≡ cc name w1 t) (trans e (sym (ContConds.ccDchoose≡ cc name w2 t)))



-- MOVE to continuity-conds
upto𝕎→≡getT : (cc : ContConds) (k : ℕ) (nm name n : Name) (w1 w2 : 𝕎·)
                → ¬ nm ≡ name
                → getT k nm w1 ≡ getT k nm w2
                → getT k nm (startChoice· n Res⊤ w1) ≡ getT k nm (startChoice· n Res⊤ w2)
upto𝕎→≡getT cc k nm name n w1 w2 diff upw with nm ≟ n
... | yes p rewrite p = ContConds.ccGstarts cc n k Res⊤ w1 w2
... | no p = trans (ContConds.ccGstartd cc nm n k Res⊤ w1 p) (trans upw (sym (ContConds.ccGstartd cc nm n k Res⊤ w2 p)))



≡pres∈ : {a b : List Name} {x : Name}
          → a ≡ b
          → x ∈ a
          → x ∈ b
≡pres∈ {a} {b} {x} e i rewrite e = i


≡pres¬∈ : {a b : List Name} {x : Name}
          → a ≡ b
          → ¬ x ∈ a
          → ¬ x ∈ b
≡pres¬∈ {a} {b} {x} e ni rewrite e = ni



sameRes-startChoice : (cc : ContConds) (n : ℕ) (w1 w2 : 𝕎·)
                      → dom𝕎· w1 ≡ dom𝕎· w2
                      → sameRes w1 w2
                      → sameRes (startChoice· n Res⊤ w1) (startChoice· n Res⊤ w2)
sameRes-startChoice cc n w1 w2 eqd same name r =
  c1 , c2
  where
    c1 : compatible· name (startChoice· n Res⊤ w1) r → compatible· name (startChoice· n Res⊤ w2) r
    c1 compat with n ≟ name
    ... | yes p rewrite p with Name∈⊎ name (dom𝕎· w1)
    ... |    inj₁ i = ContConds.ccC∈start← cc name r Res⊤ w2 (≡pres∈ eqd i) (fst (same name r) (ContConds.ccC∈start→ cc name r Res⊤ w1 i compat))
    ... |    inj₂ ni rewrite sym (ContConds.ccC¬∈start→ cc name r Res⊤ w1 ni compat) = startChoiceCompatible· Res⊤ w2 name (≡pres¬∈ eqd ni)
    c1 compat | no p = ContConds.ccC¬≡start← cc n name r Res⊤ w2 p (fst (same name r) (ContConds.ccC¬≡start→ cc n name r Res⊤ w1 p compat))

    c2 : compatible· name (startChoice· n Res⊤ w2) r → compatible· name (startChoice· n Res⊤ w1) r
    c2 compat with n ≟ name
    ... | yes p rewrite p with Name∈⊎ name (dom𝕎· w2)
    ... |    inj₁ i = ContConds.ccC∈start← cc name r Res⊤ w1 (≡pres∈ (sym eqd) i) (snd (same name r) (ContConds.ccC∈start→ cc name r Res⊤ w2 i compat))
    ... |    inj₂ ni rewrite sym (ContConds.ccC¬∈start→ cc name r Res⊤ w2 ni compat) = startChoiceCompatible· Res⊤ w1 name (≡pres¬∈ (sym eqd) ni)
    c2 compat | no p = ContConds.ccC¬≡start← cc n name r Res⊤ w1 p (snd (same name r) (ContConds.ccC¬≡start→ cc n name r Res⊤ w2 p compat))


→upto𝕎-startChoice : (cc : ContConds) {name : Name} {w1 w2 : 𝕎·} (n : Name)
                       → upto𝕎 name w1 w2
                       → upto𝕎 name (startChoice· n Res⊤ w1) (startChoice· n Res⊤ w2)
→upto𝕎-startChoice cc {name} {w1} {w2} n upw =
  mkUpto𝕎
    (ContConds.ccD≡start cc n w1 w2 (upto𝕎.upwDom upw))
    (→≡names𝕎-start cc n w1 w2 (upto𝕎.upwNames upw))
    (sameRes-startChoice cc n w1 w2 (upto𝕎.upwDom upw) (upto𝕎.upwRes upw))
    (λ nm k d → upto𝕎→≡getT cc k nm name n w1 w2 d (upto𝕎.upwGet upw nm k d))



→upto𝕎-startNewChoiceT : (cc : ContConds) {name : Name} {w1 w2 : 𝕎·} (a : Term)
                           → upto𝕎 name w1 w2
                           → upto𝕎 name (startNewChoiceT Res⊤ w1 a) (startNewChoiceT Res⊤ w2 a)
→upto𝕎-startNewChoiceT cc {name} {w1} {w2} a upw
  rewrite upto𝕎→≡newChoiceT a upw = →upto𝕎-startChoice cc (newChoiceT w2 a) upw



{--
ADD:
-- Choices are Res⊤ choices (NO!), which don't contain names
names𝕎-chooseT-Res⊤ : Set(K)
names𝕎-chooseT-Res⊤ : (name : Name) (w : 𝕎·) (t : Term)
                       → compatible· name w Res⊤
                       → names𝕎· (chooseT name w t) ≡ names𝕎· w



ADD:
→ ((k : ℕ) → getT k name w1 ≡ getT k name w2)
→ sameRes w1 w2
→ dom𝕎· w1 ≡ dom𝕎· w2
→ getT k name (chooseT name w1 t) ≡ getT k name (chooseT name w2 t)
--}



→upto𝕎getT-chooseT : (cc : ContConds) (name name' : Name) (w1 w1' : 𝕎·) (t : Term)
                 → upto𝕎 name w1 w1'
                 → upto𝕎getT name (chooseT name' w1 t) (chooseT name' w1' t)
→upto𝕎getT-chooseT cc name name' w1 w1' t upw n k dn with n ≟ name'
... | yes p rewrite p = ContConds.ccGget cc name' w1 w1' t k (λ z → upto𝕎.upwGet upw name' z dn) (upto𝕎.upwRes upw) (upto𝕎.upwDom upw) -- we need w1 and w1' to have the same restritions
... | no p = trans (ContConds.ccGcd cc k n name' w1 t p)
                   (trans (upto𝕎.upwGet upw n k dn)
                          (sym (ContConds.ccGcd cc k n name' w1' t p)))



→sameRes-chooseT : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (t : Term)
                    → sameRes w1 w2
                    → sameRes (chooseT name w1 t) (chooseT name w2 t)
→sameRes-chooseT cc name w1 w2 t same =
  sameRes-trans (sameRes-chooseT cc name w1 t)
                (sameRes-trans same (sameRes-sym (sameRes-chooseT cc name w2 t)))


→≡-names𝕎-chooseT : (cc : ContConds) (w1 w2 : 𝕎·) (name : Name) (t : Term)
                       → names𝕎· w1 ≡ names𝕎· w2
                       → names𝕎· (chooseT name w1 t) ≡ names𝕎· (chooseT name w2 t)
→≡-names𝕎-chooseT cc w1 w2 name t eqn
  rewrite ContConds.ccNchoose≡ cc name w1 t
        | ContConds.ccNchoose≡ cc name w2 t = eqn


→≡N-names𝕎-chooseT : (cc : ContConds) (w1 w2 : 𝕎·) (name : Name) (t : Term)
                       → names𝕎· w1 ≡N names𝕎· w2
                       → names𝕎· (chooseT name w1 t) ≡N names𝕎· (chooseT name w2 t)
→≡N-names𝕎-chooseT cc w1 w2 name t eqn n
  rewrite ContConds.ccNchoose≡ cc name w1 t
        | ContConds.ccNchoose≡ cc name w2 t = eqn n



upto𝕎-chooseT : (cc : ContConds) (name name' : Name) (w1 w1' : 𝕎·) (t : Term)
                 → upto𝕎 name w1 w1'
                 → upto𝕎 name (chooseT name' w1 t) (chooseT name' w1' t)
upto𝕎-chooseT cc name name' w1 w1' t upw =
  mkUpto𝕎
    (→dom𝕎-chooseT≡ cc name' w1 w1' t (upto𝕎.upwDom upw))
    (→≡-names𝕎-chooseT cc w1 w1' name' t (upto𝕎.upwNames upw)) -- we need to assume here that w1 and w1' have the same restrictions and change this requirement to be a set equality instead of a list equality
    (→sameRes-chooseT cc name' w1 w1' t (upto𝕎.upwRes upw))
    (→upto𝕎getT-chooseT cc name name' w1 w1' t upw)


step-upto𝕎 : (cc : ContConds) (name : Name) (a b : Term) (w1 w2 w1' : 𝕎·)
               → ¬ name ∈ names a
               → ¬ name ∈ names𝕎· w1
               → name ∈ dom𝕎· w1
               → step a w1 ≡ just (b , w2)
               → upto𝕎 name w1 w1'
               → Σ 𝕎· (λ w2' → step a w1' ≡ just (b , w2')
                   × upto𝕎 name w2 w2'
                   × ¬ name ∈ names b
                   × ¬ name ∈ names𝕎· w2
                   × name ∈ dom𝕎· w2)
step-upto𝕎 cc name NAT b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name QNAT b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name TNAT b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LT a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (QLT a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (NUM x) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (IFLT a a₁ a₂ a₃) b w1 w2 w1' nna nnw idom comp upw with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM a₁
... |    inj₁ (m , q) rewrite q with n <? m
... |       yes r rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈++2→¬∈1 {_} {_} {names a₂} {names a₃} {name} nna , nnw , idom
... |       no r rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈++2→¬∈2 {_} {_} {names a₂} {names a₃} {name} nna , nnw , idom
step-upto𝕎 cc name (IFLT a a₁ a₂ a₃) b w1 w2 w1' nna nnw idom comp upw | inj₁ (n , p) | inj₂ q with step⊎ a₁ w1
... |       inj₁ (a₁' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                       | fst (snd (step-upto𝕎 cc name a₁ a₁' w1 w1x w1' (¬∈++3→¬∈1 {_} {_} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    (λ x → nna (¬∈1→∈++3 {_} {_} {names a₁} {names a₂} {names a₃} {names a₁'} (fst (snd (snd (snd ind)))) x)) ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a₁ w1' ≡ just (a₁' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a₁'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a₁ a₁' w1 w1x w1' (¬∈++3→¬∈1 {_} {_} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (IFLT a a₁ a₂ a₃) b w1 w2 w1' nna nnw idom comp upw | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    (λ x → nna (¬∈1→∈++4 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {names a'} (fst (snd (snd (snd ind)))) x)) ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (SUC a) b w1 w2 w1' nna nnw idom comp upw with is-NUM a
... | inj₁ (n , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈[] {Name} {name} , nnw , idom
... | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' nna nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' nna nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (PI a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LAMBDA a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (APPLY f a) b w1 w2 w1' nna nnw idom comp upw with is-LAM f
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈names-sub {name} {a} {t} (λ x → nna (∈-++⁺ʳ (names t) x)) (λ x → nna (∈-++⁺ˡ x)) , nnw , idom
... | inj₂ x with is-CS f
... |    inj₁ (name' , p) rewrite p with is-NUM a
... |       inj₁ (n , q) rewrite q with getT⊎ n name' w1
... |          inj₁ (y , r) rewrite r | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , getT≡→map-getT≡ (λ z → nna (here (sym z))) upw r , upw ,
  (λ iy → nnw (ContConds.ccGnames cc name name' n y w1 r iy)) ,
  nnw , idom
... |          inj₂ r rewrite r = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (APPLY f a) b w1 w2 w1' nna nnw idom comp upw | inj₂ x | inj₁ (name' , p) | inj₂ y with step⊎ a w1
... |          inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                         | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' (λ z → nna (there z)) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) , (λ { (here z) → nna (here z) ; (there z) → fst (snd (snd (snd ind))) z }) , snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' (λ z → nna (there z)) nnw idom z upw
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (APPLY f a) b w1 w2 w1' nna nnw idom comp upw | inj₂ x | inj₂ y with step⊎ f w1
... | inj₁ (f' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                | fst (snd (step-upto𝕎 cc name f f' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names f} {names a} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) , (→¬∈++2 {_} {_} {name} {names f} {names a} {names f'} {names a} (λ x → fst (snd (snd (snd ind)))) (λ x → x) nna) , snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step f w1' ≡ just (f' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names f'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name f f' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names f} {names a} {name} nna) nnw idom z upw
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (FIX a) b w1 w2 w1' nna nnw idom comp upw with is-LAM a
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈names-sub {name} {FIX (LAMBDA t)} {t} nna nna , nnw , idom
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' nna nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' nna nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (LET a a₁) b w1 w2 w1' nna nnw idom comp upw with isValue⊎ a
... | inj₁ x rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw ,
  ¬∈names-sub {name} {a} {a₁} (λ x → nna (∈-++⁺ˡ x)) (λ x → nna (∈-++⁺ʳ (names a) x)) ,
  nnw , idom
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    →¬∈++2 {_} {_} {name} {names a} {names a₁} {names a'} {names a₁} (λ x → fst (snd (snd (snd ind)))) (λ x → x) nna ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (SUM a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (PAIR a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (SPREAD a a₁) b w1 w2 w1' nna nnw idom comp upw with is-PAIR a
... | inj₁ (u , v , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw ,
  ¬∈names-sub {name} {v} {sub u a₁} (λ x → nna (∈-++⁺ˡ (∈-++⁺ʳ (names u) x))) (¬∈names-sub {name} {u} {a₁} (λ x → nna (∈-++⁺ˡ (∈-++⁺ˡ x))) (λ x → nna (∈-++⁺ʳ (names u ++ names v) x))) ,
  nnw , idom
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    →¬∈++2 {_} {_} {name} {names a} {names a₁} {names a'} {names a₁} (λ x → fst (snd (snd (snd ind)))) (λ x → x) nna ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (SET a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (TUNION a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (ISECT a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (UNION a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (QTUNION a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (INL a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (INR a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (DECIDE a a₁ a₂) b w1 w2 w1' nna nnw idom comp upw with is-INL a
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈names-sub {name} {t} {a₁} (λ x → nna (∈-++⁺ˡ x)) (λ x → nna (∈-++⁺ʳ (names t) (∈-++⁺ˡ x))) , nnw , idom
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , refl , upw , ¬∈names-sub {name} {t} {a₂} (λ x → nna (∈-++⁺ˡ x)) (λ x → nna (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names a₁) x))) , nnw , idom
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                      | fst (snd (step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    →¬∈++3 {_} {_} {name} {names a} {names a₁} {names a₂} {names a'} {names a₁} {names a₂} (λ x → fst (snd (snd (snd ind)))) (λ x → x) (λ x → x) nna ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name a a' w1 w1x w1' (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {name} nna) nnw idom z upw
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (EQ a a₁ a₂) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name AX b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name FREE b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (CS x) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (NAME x) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (FRESH a) b w1 w2 w1' nna nnw idom comp upw rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl
  where
    concl : Σ 𝕎· (λ w2' → just (fresh-inst w1' a , startNewChoiceT Res⊤ w1' a) ≡ just (fresh-inst w1 a , w2')
                   × upto𝕎 name (startNewChoiceT Res⊤ w1 a) w2'
                   × ¬ name ∈ names (fresh-inst w1 a)
                   × ¬ name ∈ names𝕎· (startNewChoiceT Res⊤ w1 a)
                   × name ∈ dom𝕎· (startNewChoiceT Res⊤ w1 a))
    concl = startNewChoiceT Res⊤ w1' a ,
            ≡just (≡pair (upto𝕎→≡fresh-inst a (upto𝕎-sym _ _ _ upw)) refl) ,
            →upto𝕎-startNewChoiceT cc a upw ,
            (λ x → nna (suc→∈lowerNames (∈names-shiftNameDown-renn→ name (newChoiceT+ w1 a) a (_≤_.s≤s _≤_.z≤n) (∈dom𝕎→¬≡newChoiceT+ name w1 a idom) x))) ,
            (λ x → nnw (∈names𝕎-startNewChoiceT→ cc name w1 a x)) ,
            ContConds.ccDstart cc name w1 a idom
step-upto𝕎 cc name (CHOOSE n t) b w1 w2 w1' nna nnw idom comp upw with is-NAME n
... | inj₁ (name' , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  chooseT name' w1' t , refl ,
  upto𝕎-chooseT cc name name' w1 w1' t upw ,
  (λ ()) ,
  (λ x → nnw (names𝕎-chooseT→ cc name name' w1 t x)) ,
  dom𝕎-chooseT cc name name' w1 t idom
... | inj₂ x with step⊎ n w1
... |    inj₁ (n' , w1x , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
                                   | fst (snd (step-upto𝕎 cc name n n' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names n} {names t} {name} nna) nnw idom z upw))
  = fst ind , refl , fst (snd (snd ind)) ,
    →¬∈++2 {_} {_} {name} {names n} {names t} {names n'} {names t} (λ x → fst (snd (snd (snd ind)))) (λ x → x) nna ,
    snd (snd (snd (snd ind)))
  where
    ind : Σ 𝕎· (λ w2' → step n w1' ≡ just (n' , w2')
                   × upto𝕎 name w1x w2'
                   × ¬ name ∈ names n'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x)
    ind = step-upto𝕎 cc name n n' w1 w1x w1' (¬∈++2→¬∈1 {_} {_} {names n} {names t} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (TSQUASH a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (TTRUNC a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (TCONST a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (SUBSING a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (DUM a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (FFDEFS a a₁) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name PURE b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (UNIV x) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LIFT a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LOWER a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (SHRINK a) b w1 w2 w1' nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , refl , upw , nna , nnw , idom



steps-upto𝕎 : (cc : ContConds) (name : Name) (k : ℕ) (a b : Term) (w1 w2 w1' : 𝕎·)
               → ¬ name ∈ names a
               → ¬ name ∈ names𝕎· w1
               → name ∈ dom𝕎· w1
               → steps k (a , w1) ≡ (b , w2)
               → upto𝕎 name w1 w1'
               → Σ 𝕎· (λ w2' → steps k (a , w1') ≡ (b , w2')
                   × upto𝕎 name w2 w2'
                   × ¬ name ∈ names b
                   × ¬ name ∈ names𝕎· w2
                   × name ∈ dom𝕎· w2)
steps-upto𝕎 cc name k a b w1 w2 w1' nna nnw idom comp upw = {!!}



{--
→ΣstepsUpdRel2-upd : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w1 w : 𝕎·}
                     → ¬ name ∈ names f
                     → # f
                     → # g
                     → compatible· name w1 Res⊤
                     → compatible· name w Res⊤
                     → ∀𝕎-get0-NUM w1 name
                     → updRel2 name f g a b
                     → upto𝕎 name w1 w
                     → ∀𝕎 w (λ w' _ → (k : ℕ) → k < n → ∀𝕎-⇓∼ℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                     → stepsPresUpdRel2 n name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
                     → Σ (ΣstepsUpdRel2 name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 (APPLY (force g) b) w)
                          (λ x → 0 < fst (snd x))
→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {a} {b} {w1} {w} nnf cf cg compat compat' wgt0 u upw eqn (k , v , w2 , comp , isv , ish , inw , ind) =
  (k2 + k3 , k5 + k6 , NUM i , NUM i , w1a' , w1a , comp2b , compgc , updRel2-NUM i , upto𝕎-sym name w1a w1a' upw2) ,
  steps-APPLY-val→ {k5 + k6} {force g} {b} {NUM i} {w} {w1a} tt compgc
  where
    c : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1' → Σ ℕ (λ m → Σ ℕ (λ m' →
           k1 < k
           × k2 < k
           × getT 0 name w1' ≡ just (NUM m')
           × ssteps k1 (a , w1) ≡ just (NUM m , w1')
           × steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))))))
    c = upd-decomp cf wgt0 comp isv
-- We need to know that m is less than n

    k1 : ℕ
    k1 = fst c

    k2 : ℕ
    k2 = fst (snd c)

    w1' : 𝕎·
    w1' = fst (snd (snd c))

    m : ℕ
    m = fst (snd (snd (snd c)))

    m' : ℕ
    m' = fst (snd (snd (snd (snd c))))

    ltk1 : k1 < k
    ltk1 = fst (snd (snd (snd (snd (snd c)))))

    ltk2 : k2 < k
    ltk2 = fst (snd (snd (snd (snd (snd (snd c))))))

    gt0 : getT 0 name w1' ≡ just (NUM m')
    gt0 = fst (snd (snd (snd (snd (snd (snd (snd c)))))))

    comp1 : ssteps k1 (a , w1) ≡ just (NUM m , w1')
    comp1 = fst (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    comp1b : steps k1 (a , w1) ≡ (NUM m , w1')
    comp1b = ssteps→steps {k1} {a} {NUM m} {w1} {w1'} comp1

    comp2 : steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m)
    comp2 = snd (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    e1 : w1 ⊑· w1'
    e1 = steps→⊑ k1 a (NUM m) comp1b

    e2 : w1 ⊑· chooseT0if name w1' m' m
    e2 = ⊑-trans· e1 (⊑chooseT0if {w1'} {name} {m'} {m})

    ltm : m < n
    ltm = isHighestℕ-updBody→< gc {n} {name} {f} {k1} {k} {a} {v} {m} {w1} {w1'} {w2} cf compat comp1b comp isv ish

    ish1 : isHighestℕ {k1} {w1} {w1'} {a} {NUM m} n name comp1b
    ish1 = isHighestℕ-LET→ {n} {k1} {k} {name} {a} {SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))} {NUM m} {v} {w1} {w1'} {w2} comp1b comp isv ish

    inw1 : ∈names𝕎 {k1} {w1} {w1'} {a} {NUM m} name comp1b
    inw1 = ∈names𝕎-LET→ {k1} {k} {name} {a} {SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))} {NUM m} {v} {w1} {w1'} {w2} comp1b comp isv inw

    indb : Σ ℕ (λ k' → Σ 𝕎· (λ w' → steps k' (b , w) ≡ (NUM m , w') × upto𝕎 name w1' w'))
    indb = Σsteps-updRel2-NUM→ (ind k1 (<⇒≤ ltk1) {a} {b} {NUM m} {w1} {w1'} {w} u upw compat compat' wgt0 eqn comp1b ish1 inw1 tt)

    k4 : ℕ
    k4 = fst indb

    w1x : 𝕎·
    w1x = fst (snd indb)

    cb : steps k4 (b , w) ≡ (NUM m , w1x)
    cb = fst (snd (snd indb))

    upw1 : upto𝕎 name w1' w1x
    upw1 = snd (snd (snd indb))

    compg : APPLY (force g) b ⇓ APPLY g (NUM m) from w to w1x
    compg = →APPLY-force⇓APPLY-NUM {m} {g} {b} {w} {w1x} cg (k4 , cb)

    k5 : ℕ
    k5 = fst compg

    compgb : steps k5 (APPLY (force g) b , w) ≡ (APPLY g (NUM m) , w1x)
    compgb = snd compg

    e1x : w ⊑· w1x
    e1x = steps→⊑ k4 b (NUM m) cb

    q : ⇓∼ℕ w1x (APPLY f (NUM m)) (APPLY g (NUM m))
    q = lower (eqn w (⊑-refl· _) m ltm w1x e1x)

    i : ℕ
    i = fst q

    c1 : Σ 𝕎· (λ w1a → APPLY f (NUM m) ⇓ NUM i from w1x to w1a
                       × APPLY g (NUM m) ⇓ NUM i from w1x to w1a)
    c1 = snd q

    w1a : 𝕎·
    w1a = fst c1

    k3 : ℕ
    k3 = fst (fst (snd c1))

    c1a : steps k3 (APPLY f (NUM m) , w1x) ≡ (NUM i , w1a)
    c1a = snd (fst (snd c1))

    k6 : ℕ
    k6 = fst (snd (snd c1))

    c1b : steps k6 (APPLY g (NUM m) , w1x) ≡ (NUM i , w1a)
    c1b = snd (snd (snd c1))

    upwc : upto𝕎 name w1x (chooseT0if name w1' m' m)
    upwc = upto𝕎-trans name w1x w1' (chooseT0if name w1' m' m) (upto𝕎-sym name w1' w1x upw1) (upto𝕎-chooseT0if cc name w1' m' m)

    nnw1x : ¬ name ∈ names𝕎· w1x
    nnw1x = {!!}

    idomw1x : name ∈ dom𝕎· w1x
    idomw1x = {!!}

-- TODO: prove this result (because ¬ name ∈ names t + the other assumptions)
-- from c1a and upw1 because (upto𝕎 name w1x (chooseT0if name w1' m' m))
    c1ab : Σ 𝕎· (λ w1a' → steps k3 (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a')
                           × upto𝕎 name w1a w1a')
    c1ab = steps-upto𝕎
             name k3 (APPLY f (NUM m)) (NUM i) w1x w1a (chooseT0if name w1' m' m)
             (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
             nnw1x idomw1x
             c1a upwc

    w1a' : 𝕎·
    w1a' = fst c1ab

    c1c : steps k3 (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a')
    c1c = fst (snd c1ab)

    upw2 : upto𝕎 name w1a w1a'
    upw2 = snd (snd c1ab)

    comp2b : steps (k2 + k3) (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (NUM i , w1a')
    comp2b = steps-trans+ {k2} {k3} {LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} {NUM i} {w1} {chooseT0if name w1' m' m} {w1a'} comp2 c1c

    compgc : steps (k5 + k6) (APPLY (force g) b , w) ≡ (NUM i , w1a)
    compgc = steps-trans+ {k5} {k6} {APPLY (force g) b} {APPLY g (NUM m)} {NUM i} {w} {w1x} {w1a} compgb c1b



step-updRel2 : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
              {a b x : Term} {w1 w2 w : 𝕎·}
              → ¬ name ∈ names f
              → ¬ name ∈ names g
              → # f
              → # g
              → step a w1 ≡ just (x , w2)
              → stepsPresUpdRel2 n name f g x w2
              → updRel2 name f g a b
              → upto𝕎 name w1 w
              → getT≤ℕ w1 n name
              → ¬ name ∈ names𝕎· w1
              → name ∈ dom𝕎· w1
              → compatible· name w1 Res⊤
              → compatible· name w Res⊤
              → ∀𝕎-get0-NUM w1 name
              → ∀𝕎 w (λ w' _ → (k : ℕ) → k < n → ∀𝕎-⇓∼ℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
              → ΣstepsUpdRel2 name f g x w2 b w
step-updRel2 cc gc {n} {name} {f} {g} {.NAT} {.NAT} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-NAT upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , w , refl , refl , updRel2-NAT , upw
step-updRel2 cc gc {n} {name} {f} {g} {.QNAT} {.QNAT} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-QNAT upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , w , refl , refl , updRel2-QNAT , upw
step-updRel2 cc gc {n} {name} {f} {g} {.TNAT} {.TNAT} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-TNAT upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TNAT , TNAT , w1 , w , refl , refl , updRel2-TNAT , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-LT a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , w , refl , refl , updRel2-LT _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-QLT a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , w , refl , refl , updRel2-QLT _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(NUM x₁)} {.(NUM x₁)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-NUM x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM _ , NUM _ , w1 , w , refl , refl , updRel2-NUM _ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SUC a₁)} {.(SUC a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-SUC a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-PI a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , w , refl , refl , updRel2-PI _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-LAMBDA a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , w , refl , refl , updRel2-LAMBDA _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn with is-LAM a₁
... | inj₁ (t , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl d
  where
    d : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g t u)
        ⊎ (t ≡ updBody name f × a₂ ≡ force g)
    d = updRel2-LAMBDAₗ→ r

    concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g t u)
            ⊎ (t ≡ updBody name f × a₂ ≡ force g)
            → ΣstepsUpdRel2 name f g (sub b₁ t) w1 (APPLY a₂ b₂) w
    concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub b₁ t , sub b₂ u , w1 , w , refl , refl , updRel2-sub cf cg ur r₁ , upw
    concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c2
      where
        ind' : stepsPresUpdRel2 n name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        ind' rewrite e1 | e2 | sub-upd name f b₁ cf = ind

        c1 : ΣstepsUpdRel2 name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 (APPLY (force g) b₂) w
        c1 = fst (→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {b₁} {b₂} {w1} {w} nnf cf cg compat compat' wgt0 r₁ upw eqn ind')

        c2 : ΣstepsUpdRel2 name f g (sub b₁ (updBody name f)) w1 (APPLY (force g) b₂) w
        c2 rewrite sub-upd name f b₁ cf = c1
... | inj₂ q with is-CS a₁
... |    inj₁ (name' , np) rewrite np | updRel2-CSₗ→ r with is-NUM b₁
... |       inj₁ (k , nq) rewrite nq | updRel2-NUMₗ→ r₁ with getT⊎ k name' w1
... |          inj₁ (c , nr) rewrite nr | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , 1 , c , c , w1 , w , refl , {!!} ,
  (updRel2-refl {name} {f} {g} {c} {!!}) ,
  upw --Data.Maybe.map (λ t → t , w) (getT n name w)
... |          inj₂ nr rewrite nr = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn | inj₂ q | inj₁ (name' , np) | inj₂ y with step⊎ b₁ w1
... |          inj₁ (b₁' , w1' , z) rewrite z = {!!} --ret (APPLY (CS name) u) w'
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn | inj₂ q | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-APPLY₁ r₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1' a₂ w
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel2-APPLY₁→ ind) r upw gtn nnw idom compat compat' wgt0 eqn
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(FIX a₁)} {.(FIX a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-FIX a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-LET a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-SUM a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , w , refl , refl , updRel2-SUM _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-PAIR a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-SPREAD a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-SET a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , w , refl , refl , updRel2-SET _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-ISECT a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , w , refl , refl , updRel2-ISECT _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-TUNION a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w , refl , refl , updRel2-TUNION _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-UNION a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , w , refl , refl , updRel2-UNION _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-QTUNION a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w , refl , refl , updRel2-QTUNION _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(INL a₁)} {.(INL a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-INL a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , w , refl , refl , updRel2-INL _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(INR a₁)} {.(INR a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-INR a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , w , refl , refl , updRel2-INR _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.AX} {.AX} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-AX upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , w , refl , refl , updRel2-AX , upw
step-updRel2 cc gc {n} {name} {f} {g} {.FREE} {.FREE} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-FREE upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , w , refl , refl , updRel2-FREE , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(CS name')} {.(CS name')} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-CS name' x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , CS _ , CS _ , w1 , w , refl , refl , updRel2-CS _ x₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(NAME name')} {.(NAME name')} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-NAME name' x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAME _ , NAME _ , w1 , w , refl , refl , updRel2-NAME _ x₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(FRESH a)} {.(FRESH b)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-FRESH a b r) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-CHOOSE a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-TSQUASH a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , w , refl , refl , updRel2-TSQUASH _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-TTRUNC a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , w , refl , refl , updRel2-TTRUNC _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(TCONST a₁)} {.(TCONST a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-TCONST a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TCONST a₁ , TCONST a₂ , w1 , w , refl , refl , updRel2-TCONST _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(SUBSING a₁)} {.(SUBSING a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-SUBSING a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , w , refl , refl , updRel2-SUBSING _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.PURE} {.PURE} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-PURE upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PURE , PURE , w1 , w , refl , refl , updRel2-PURE , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(DUM a₁)} {.(DUM a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-DUM a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , DUM a₁ , DUM a₂ , w1 , w , refl , refl , updRel2-DUM _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-FFDEFS a₁ a₂ b₁ b₂ r r₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w , refl , refl , updRel2-FFDEFS _ _ _ _ r r₁ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(UNIV x₁)} {.(UNIV x₁)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-UNIV x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV _ , UNIV _ , w1 , w , refl , refl , updRel2-UNIV _ , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(LIFT a₁)} {.(LIFT a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-LIFT a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , w , refl , refl , updRel2-LIFT _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(LOWER a₁)} {.(LOWER a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-LOWER a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , w , refl , refl , updRel2-LOWER _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(SHRINK a₁)} {.(SHRINK a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel2-SHRINK a₁ a₂ r) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , w , refl , refl , updRel2-SHRINK _ _ r , upw
step-updRel2 cc gc {n} {name} {f} {g} {.(upd name f)} {.(force g)} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel2-upd upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , upd name f , force g , w1 , w , refl , refl , updRel2-upd , upw


{--
steps-updRel2-aux : (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
                   → ¬ name ∈ names f
                   → ¬ name ∈ names g
                   → # f
                   → # g
                   → (k : ℕ)
                   → (ind : (k' : ℕ) → k' < k → presUpdRel2 n name f g k')
                   → presUpdRel2 n name f g k
steps-updRel2-aux gc {n} {name} {f} {g} nnf nng cf cg 0 ind {a} {b} {v} {w1} {w2} {w} r compat wgt0 eqw comp ish inw isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , b , refl , r
steps-updRel2-aux gc {n} {name} {f} {g} nnf nng cf cg (suc k) ind {a} {b} {v} {w1} {w2} {w} r compat wgt0 eqw comp ish inw isv
  with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  k2 + k4 , v' , steps-trans+ {k2} {k4} {b} {y2} {v'} {w} {w} {w} comp2 comp4 , ur'
  where
    ind0 : (k' : ℕ) → k' < suc k → presUpdRel2 n name f g k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    spres : stepsPresUpdRel2 n name f g a' w1'
    spres = k , v , w2 , comp , isv , snd ish , snd (snd inw) , ind1

    s : ΣstepsUpdRel2 name f g a' w1' b w
    s = step-updRel2 cc gc {n} {name} {f} {g} {a} {b} {a'} {w1} {w1'} {w} nnf nng cf cg z spres r (fst ish) (fst inw) (fst (snd inw)) compat wgt0 eqw

    k1 : ℕ
    k1 = fst s

    k2 : ℕ
    k2 = fst (snd s)

    y1 : Term
    y1 = fst (snd (snd s))

    y2 : Term
    y2 = fst (snd (snd (snd s)))

    w3 : 𝕎·
    w3 = fst (snd (snd (snd (snd s))))

    comp1 : steps k1 (a' , w1') ≡ (y1 , w3)
    comp1 = fst (snd (snd (snd (snd (snd s)))))

    comp2 : steps k2 (b , w) ≡ (y2 , w)
    comp2 = fst (snd (snd (snd (snd (snd (snd s))))))

    ur : updRel2 name f g y1 y2
    ur = snd (snd (snd (snd (snd (snd (snd s))))))

    q : Σ ℕ (λ k3 → k3 ≤ k × Σ (steps k3 (y1 , w3) ≡ (v , w2)) (λ comp' →
                  (isHighestℕ {k} {w1'} {w2} {a'} {v} n name comp
                   → isHighestℕ {k3} {w3} {w2} {y1} {v} n name comp')
                  × (∈names𝕎 {k} {w1'} {w2} {a'} {v} name comp
                     → ∈names𝕎 {k3} {w3} {w2} {y1} {v} name comp')))
    q = steps-decomp-isHighestℕ2 {w1'} {w3} {w2} {a'} {y1} {v} {k} {k1} n name isv comp1 comp

    k3 : ℕ
    k3 = fst q

    ltk2 : k3 ≤ k
    ltk2 = fst (snd q)

    comp3 : steps k3 (y1 , w3) ≡ (v , w2)
    comp3 = fst (snd (snd q))

    ish' : isHighestℕ {k3} {w3} {w2} {y1} {v} n name comp3
    ish' = fst (snd (snd (snd q))) (snd ish)

    inw' : ∈names𝕎 {k3} {w3} {w2} {y1} {v} name comp3
    inw' = snd (snd (snd (snd q))) (snd (snd inw))

    e3 : w1 ⊑· w3
    e3 = ⊑-trans· (step⊑ {w1} {w1'} {a} {a'} z) (steps→⊑ k1 a' y1 {w1'} {w3} comp1)

    c : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (y2 , w) ≡ (v' , w) × updRel2 name f g v v'))
    c = ind1 k3 ltk2 {y1} {y2} {v} {w3} {w2} {w} ur (⊑-compatible· e3 compat) (∀𝕎-mon e3 wgt0) (∀𝕎-mon e3 eqw) comp3 ish' inw' isv

    k4 : ℕ
    k4 = fst c

    v' : Term
    v' = fst (snd c)

    comp4 : steps k4 (y2 , w) ≡ (v' , w)
    comp4 = fst (snd (snd c))

    ur' : updRel2 name f g v v'
    ur' = snd (snd (snd c))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal a w1 isv =
  ⊥-elim (¬just≡nothing z)
--}


eqfgq-aux : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
            {i : ℕ} {w1 w1s' w2 : 𝕎·} {F f g : CTerm} {name : Name}
            {k : ℕ} {v : Term} {j : ℕ} {tn : ℕ}
            → ¬ name ∈ names ⌜ f ⌝
            → ¬ name ∈ names ⌜ F ⌝
            → ¬ name ∈ names𝕎· w1s'
            → name ∈ dom𝕎· w1s'
            → compatible· name w1s' Res⊤
            → ∀𝕎-get0-NUM w1s' name
            → getT 0 name w2 ≡ just (NUM j)
            → tn ≡ suc j
            → isValue v
            → steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1s') ≡ (v , w2)
            → (k' : ℕ) → #APPLY F (#force f) #⇓ #NUM k' at w1 → #APPLY F (#force g) #⇓ #NUM k' at w1
eqfgq-aux cc cn kb gc {i} {w1} {w1s'} {w2} {F} {f} {g} {name} {k} {v} {j} {tn} nnf nnF nnw1s' idomw1s' compat1 wgt0 g0 eqj isvv compa k' c =
  {!!}
  where
    uF : updCtxt2 name ⌜ f ⌝ ⌜ F ⌝
    uF = updCtxt2-refl name ⌜ f ⌝ ⌜ F ⌝ nnF

    pish : (getT≤ℕ w2 tn name → isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa)
           × ∈names𝕎 {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} name compa
    pish = steps-sat-isHighestℕ2
             cc gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f)
             {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
             compa isvv (updCtxt2-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) uF updCtxt2-upd)
             compat1 wgt0 nnw1s' idomw1s'

    gt0 : getT≤ℕ w2 tn name
    gt0 = j , g0 , ≡suc→< eqj

    ish : isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
    ish = fst pish gt0

{--
        compg0 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1) × updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'))
        compg0 = ? --steps-updRel-app gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {k} {w1'} {w2} {w1} nnF nnf nng (CTerm.closed f) (CTerm.closed g) compat1 wgt0 (∀𝕎-mon e1' eqb3) compa ish isvv

        k' : ℕ
        k' = fst compg0

        v' : Term
        v' = fst (snd compg0)

        compg1 : steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
        compg1 = fst (snd (snd compg0))

        ur :  updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'
        ur = snd (snd (snd compg0))

        equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
        equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}



{--
eqfgq : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
        {i : ℕ} {w : 𝕎·} {F f g : CTerm}
        → #¬Names g
        → (∈F : ∈Type i w #BAIRE→NAT F)
        → (∈f : ∈Type i w #BAIRE f)
        → ∈Type i w #BAIRE g
        → smallestMod cn kb gc i w F f ∈F ∈f
        → equalInType i w (#QBAIREn (#νtestMup F f)) f g
--       ((n : ℕ) → n < ? → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
        → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
eqfgq cc cn kb gc {i} {w} {F} {f} {g} nng ∈F ∈f ∈g smod eqb =
  equalInType-trans (equalInType-APPLY-force ∈F ∈f) (equalInType-trans eqf (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
  where
    eqb1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#QNATn (#νtestMup F f)) a₁ a₂
                         → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    eqb1 = equalInType-FUN→ (≡CTerm→equalInType (≡QBAIREn (#νtestMup F f)) eqb)

    eqb2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                         → □· w' (λ w'' _ → Σ ℕ (λ tn → Σ ℕ (λ k → #νtestMup F f #⇓ #NUM tn at w'' × a₁ #⇛ #NUM k at w'' × a₂ #⇛ #NUM k at w'' × k < tn)))
                         → □· w' (λ w'' _ → NATeq w'' (#APPLY f a₁) (#APPLY g a₂)))
    eqb2 w1 e1 a₁ a₂ eqa = equalInType-NAT→ i w1 (#APPLY f a₁) (#APPLY g a₂) (eqb1 w1 e1 a₁ a₂ (→equalInType-QNATn (testM-QNAT cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)) eqa))

-- NOTE: It is not clear how this could work since to prove compg0 below we need to know that f and g compute to the same number
-- on the same input, as long as this input is less than the modulus of F at f. However, to use eqb2 for that we would have to
-- prove that this input is less than all possible moduli of continuity for all extensions...
-- Counter-example?

    eqb3 : ∀𝕎 w (λ w' _ → (k : ℕ)
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMup F f #⇓ #NUM n at w'' × k < n)))
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb3 w1 e1 k comp = kb z w1 (⊑-refl· _)
      where
        z : □· w1 (λ w'' _ → NATeq w'' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        z = eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M λ w2 e2 → fst (lower (comp w2 e2)) , k , fst (snd (lower (comp w2 e2))) , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , snd (snd (lower (comp w2 e2))))

 --eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w2 e2 → k , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , ltk))

{--    neqt : NATeq w (#νtestM F f) (#νtestM F f)
    neqt = νtestM-NAT cn kb gc i w F f nnF nnf ∈F ∈f

    tn : ℕ
    tn = fst neqt

    x : NATeq w (#νtestM F f) (#NUM tn)
    x = tn , fst (snd neqt) , compAllRefl _ _

    cx : #νtestM F f #⇛ #NUM tn at w
    cx = NATeq→⇛ {w} {#νtestM F f} x
--}

    inn : ∈Type i w #NAT (#APPLY F (#force f))
    inn = equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f))

    aw : ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) ((k : ℕ) → #APPLY F (#force f) #⇓ #NUM k at w' → #APPLY F (#force g) #⇓ #NUM k at w'))
    aw w1 e1 = lift imp
      where
        w1' : 𝕎·
        w1' = fst smod

        e1' : w ⊑· w1'
        e1' = fst (snd smod)

        sma : smallestModAux cn kb gc i w F f w1' e1' ∈F ∈f
        sma = {!!} --snd (snd smod)

        eqb4 : Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMup F f #⇓ #NUM n from w1' to w2
                          × ∀𝕎 w1' (λ w' _ → (k : ℕ) → k < n
                                            → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
        eqb4 = smallestModAux→NATeq cn kb gc {i} {w} {F} {f} {g} {w1'} {e1'} ∈F ∈f {!!} {--sma--} eqb3

        tn : ℕ
        tn = fst eqb4

        w2 : 𝕎·
        w2 = fst (snd eqb4)

        compt : νtestMup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1' to w2
        compt = fst (snd (snd eqb4))

        eqb5 : ∀𝕎 w1' (λ w' _ → (k : ℕ) → k < tn
                               → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        eqb5 = snd (snd (snd eqb4))

        w1s : 𝕎·
        w1s = startNewChoiceT Res⊤ w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

        name : Name
        name = newChoiceT w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

        compu : Σ Term (λ v → Σ ℕ (λ j →
                 APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v from (chooseT name w1s (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM j)
                 × tn ≡ suc j
                 × compatible· name w1s Res⊤))
        compu = νtestM⇓→ cn {w1'} {w2} {⌜ F ⌝} {⌜ f ⌝} {tn} (CTerm.closed F) (CTerm.closed f) compt

        v : Term
        v = fst compu

        j : ℕ
        j = fst (snd compu)

        w1s' : 𝕎·
        w1s' = chooseT name w1s (NUM 0)

        e0' : w1' ⊑· w1s'
        e0' = ⊑-trans· (startNewChoiceT⊏ Res⊤ w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝)) (choose⊑· name w1s (T→ℂ· (NUM 0)))

        e0'' : w ⊑· w1s'
        e0'' = ⊑-trans· e1' e0'

        k : ℕ
        k = fst (fst (snd (snd compu)))

        compa : steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1s') ≡ (v , w2)
        compa = snd (fst (snd (snd compu)))

        isvv : isValue v
        isvv = fst (snd (snd (snd compu)))

        g0 : getT 0 name w2 ≡ just (NUM j)
        g0 = fst (snd (snd (snd (snd compu))))

        eqj : tn ≡ suc j
        eqj = fst (snd (snd (snd (snd (snd compu)))))

        compat : compatible· name w1s Res⊤
        compat = snd (snd (snd (snd (snd (snd compu)))))

        compat1 : compatible· name w1s' Res⊤
        compat1 = ⊑-compatible· (choose⊑· name w1s (T→ℂ· (NUM 0))) compat

        wgt0 : ∀𝕎-get0-NUM w1s' name
        wgt0 = cn name w1s 0 compat

        nnf : ¬ name ∈ names ⌜ f ⌝
        nnf = ¬newChoiceT-testMup∈names-f w1' ⌜ F ⌝ ⌜ f ⌝

        nnF : ¬ name ∈ names ⌜ F ⌝
        nnF = ¬newChoiceT-testMup∈names-F w1' ⌜ F ⌝ ⌜ f ⌝

        uF : updCtxt2 name ⌜ f ⌝ ⌜ F ⌝
        uF = updCtxt2-refl name ⌜ f ⌝ ⌜ F ⌝ nnF

        nnw1' : ¬ name ∈ names𝕎· w1'
        nnw1' = ¬newChoiceT-testMup∈names𝕎 w1' ⌜ F ⌝ ⌜ f ⌝

        nnw1s' : ¬ name ∈ names𝕎· w1s'
        nnw1s' = λ i → nnw1' (ContConds.ccNstart cc name w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝) (ContConds.ccNchoose cc name name w1s (NUM 0) (λ ()) i))

        idomw1s' : name ∈ dom𝕎· w1s'
        idomw1s' = dom𝕎-chooseT cc name name w1s (NUM 0) (ContConds.ccNchoice cc w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝))

        pish : (getT≤ℕ w2 tn name → isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa)
               × ∈names𝕎 {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} name compa
        pish = {!steps-sat-isHighestℕ2-unf
                 cc gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f)
                 {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
                 compa isvv (updCtxt2-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) uF updCtxt2-upd)
                 compat1 wgt0 nnw1s' idomw1s'!}

        gt0 : getT≤ℕ w2 tn name
        gt0 = j , g0 , {!≡suc→< eqj!}

        ish : isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
        ish = {!!} {--fst pish ?--}

        -- TODO: this is what we have to prove
        imp : (k : ℕ) → #APPLY F (#force f) #⇓ #NUM k at w1 → #APPLY F (#force g) #⇓ #NUM k at w1
        imp k' c = {!!}

{--
        compg0 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1) × updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'))
        compg0 = ? --steps-updRel-app gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {k} {w1'} {w2} {w1} nnF nnf nng (CTerm.closed f) (CTerm.closed g) compat1 wgt0 (∀𝕎-mon e1' eqb3) compa ish isvv

        k' : ℕ
        k' = fst compg0

        v' : Term
        v' = fst (snd compg0)

        compg1 : steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
        compg1 = fst (snd (snd compg0))

        ur :  updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'
        ur = snd (snd (snd compg0))

        equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
        equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}

--      n , comp1 ,
--      {!!} --¬Names→⇓→⇛ w1 w1 ⌜ #APPLY F (#force g) ⌝ (NUM n) (#¬Names-APPLY {F} {#force g} nnF (#¬Names-force {g} nng)) compg
{--      where
        cxb : Σ 𝕎· (λ w2 → νtestM ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1 to w2)
        cxb = ⇓→from-to (lower (cx w1 e1))

        w2 : 𝕎·
        w2 = fst cxb

        compt : νtestM ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1 to w2
        compt = snd cxb

        w1s : 𝕎·
        w1s = startNewChoiceT Res⊤ w1 (testM 0 ⌜ F ⌝ ⌜ f ⌝)

        compu : Σ Name (λ name → Σ Term (λ v → Σ ℕ (λ j →
                 APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v from (chooseT name w1s (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM j)
                 × tn ≡ suc j
                 × compatible· name w1s Res⊤)))
        compu = #νtestM⇓→ cn {w1} {w2} {⌜ F ⌝} {⌜ f ⌝} {tn} (CTerm.closed F) (CTerm.closed f) nnF nnf compt

        name : Name
        name = fst compu

        v : Term
        v = fst (snd compu)

        j : ℕ
        j = fst (snd (snd compu))

        w1' : 𝕎·
        w1' = chooseT name w1s (NUM 0)

        e0' : w1 ⊑· w1'
        e0' = ⊑-trans· (startNewChoiceT⊏ Res⊤ w1 (testM 0 ⌜ F ⌝ ⌜ f ⌝)) (choose⊑· name w1s (T→ℂ· (NUM 0)))

        e1' : w ⊑· w1'
        e1' = ⊑-trans· e1 e0'

        k : ℕ
        k = fst (fst (snd (snd (snd compu))))

        compa : steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1') ≡ (v , w2)
        compa = snd (fst (snd (snd (snd compu))))

        isvv : isValue v
        isvv = fst (snd (snd (snd (snd compu))))

        g0 : getT 0 name w2 ≡ just (NUM j)
        g0 = fst (snd (snd (snd (snd (snd compu)))))

        eqj : tn ≡ suc j
        eqj = fst (snd (snd (snd (snd (snd (snd compu))))))

        compat : compatible· name w1s Res⊤
        compat = snd (snd (snd (snd (snd (snd (snd compu))))))

        compat1 : compatible· name w1' Res⊤
        compat1 = ⊑-compatible· (choose⊑· name w1s (T→ℂ· (NUM 0))) compat

        wgt0 : ∀𝕎-get0-NUM w1' name
        wgt0 = cn name w1s 0 compat

        ish : isHighestℕ {k} {w1'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
        ish = steps-sat-isHighestℕ
                gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f) {w1'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
                compa isvv (updCtxt-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) (¬Names→updCtxt {name} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd)
                compat1
                wgt0
                (j , g0 , ≡suc→< eqj)

        compg0 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1) × updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'))
        compg0 = steps-updRel-app gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {k} {w1'} {w2} {w1} nnF nnf nng (CTerm.closed f) (CTerm.closed g) compat1 wgt0 (∀𝕎-mon e1' eqb3) compa ish isvv

        k' : ℕ
        k' = fst compg0

        v' : Term
        v' = fst (snd compg0)

        compg1 : steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
        compg1 = fst (snd (snd compg0))

        ur :  updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'
        ur = snd (snd (snd compg0))

        equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
        equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}

    eqf : equalInType i w #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqf = →equalInType-NAT
            i w (#APPLY F (#force f)) (#APPLY F (#force g))
            (Mod.∀𝕎-□Func M
              (→∀𝕎-NATeq-NATeq w (#APPLY F (#force f)) (#APPLY F (#force g)) aw)
              (equalInType-NAT→ i w (#APPLY F (#force f)) (#APPLY F (#force f)) inn))
--}



{--
continuityQBody : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
                  (i : ℕ) (w : 𝕎·) (F f : CTerm)
                  → ∈Type i w #BAIRE→NAT F
                  → ∈Type i w #BAIRE f
                  → ∈Type i w (#contQBody F f) (#PAIR (#νtestMup F f) #lam3AX)
continuityQBody cn kb gc i w F f ∈F ∈f =
  ≡CTerm→equalInType (sym (#contQBody≡ F f)) h0
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #QNAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestMup F f) #lam3AX)
                                (#PAIR (#νtestMup F f) #lam3AX))
    aw w1 e1 =
      #νtestMup F f , #νtestMup F f , #lam3AX , #lam3AX ,
      testM-QNAT cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) ,
      #compAllRefl (#PAIR (#νtestMup F f) #lam3AX) w1 ,
      #compAllRefl (#PAIR (#νtestMup F f) #lam3AX) w1 ,
      eql1
      where
        ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                             → equalTypes i w2
                                           (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f g₁ (#QBAIREn (#νtestMup F f))) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                           (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f g₂ (#QBAIREn (#νtestMup F f))) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT))))
        ea2 w2 e2 g₁ g₂ eg =
          eqTypesFUN←
            (eqTypesFFDEFS← eqTypesBAIRE eg)
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesQBAIREn i w2 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                          (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) eg))
              (eqTypesEQ← eqTypesNAT
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

        aw3 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                              → equalInType i w2 (#FUN (#FFDEFS #BAIRE g₁)
                                                        (#FUN (#EQ f g₁ (#QBAIREn (#νtestMup F f)))
                                                              (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                             (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
        aw3 w2 e2 g₁ g₂ eg =
          equalInType-FUN
            (eqTypesFFDEFS← eqTypesBAIRE (equalInType-refl eg))
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesQBAIREn i w2 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                           (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                           (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-refl eg)))
              (eqTypesEQ← eqTypesNAT
                           (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                           (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-refl eg))))
            aw4
          where
            aw4 : ∀𝕎 w2 (λ w' _ → (x₁ x₂ : CTerm)
                                 → equalInType i w' (#FFDEFS #BAIRE g₁) x₁ x₂
                                 → equalInType i w' (#FUN (#EQ f g₁ (#QBAIREn (#νtestMup F f)))
                                                           (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                                     (#APPLY (#APPLY #lam3AX g₁) x₁)
                                                     (#APPLY (#APPLY #lam3AX g₂) x₂))
            aw4 w3 e3 x₁ x₂ ex =
              equalInType-FUN
                (eqTypesEQ← (→equalTypesQBAIREn i w3 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w3 F f (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                             (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w3 F f (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                             (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w3 F f (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-refl (equalInType-mon eg w3 e3))))
                (eqTypesEQ← eqTypesNAT
                             (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                             (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-refl (equalInType-mon eg w3 e3))))
                aw5
              where
                aw5 : ∀𝕎 w3 (λ w' _ → (y₁ y₂ : CTerm)
                                     → equalInType i w' (#EQ f g₁ (#QBAIREn (#νtestMup F f))) y₁ y₂
                                     → equalInType i w' (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)
                                                         (#APPLY (#APPLY (#APPLY #lam3AX g₁) x₁) y₁)
                                                         (#APPLY (#APPLY (#APPLY #lam3AX g₂) x₂) y₂))
                aw5 w4 e4 y₁ y₂ ey =
                  equalInType-EQ
                    eqTypesNAT
                    concl
                  where
                    hyp : □· w4 (λ w5 _ → equalInType i w5 (#QBAIREn (#νtestMup F f)) f g₁)
                    hyp = equalInType-EQ→ ey

                    ff : □· w3 (λ w' _ → FFDEFSeq g₁ (equalInType i w' #BAIRE) w' x₁ x₂)
                    ff = equalInTypeFFDEFS→ ex

                    aw6 : ∀𝕎 w4 (λ w' e' → equalInType i w' (#QBAIREn (#νtestMup F f)) f g₁
                                          → ↑wPred (λ w'' _ → FFDEFSeq g₁ (equalInType i w'' #BAIRE) w'' x₁ x₂) e4 w' e'
                                          → equalInType i w' #NAT (#APPLY F f) (#APPLY F g₁))
                    aw6 w5 e5 h1 (g , h2 , nng) = equalInType-trans cc (∈BAIRE→NAT→ (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-sym h2))
                      where
                        h3 : equalInType i w5 (#QBAIREn (#νtestMup F f)) f g
                        h3 = equalInType-QBAIREn-BAIRE-trans h2 h1 (testM-QNAT cn kb gc i w5 F f (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))))

                        cc : equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)
                        cc = {!!} {--eqfg cn kb gc {i} {w5} {F} {f} {g} nnF nnf nng
                                  (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))))
                                  (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))))
                                  (equalInType-refl (equalInType-sym h2))
                                  h3--}

                    concl : □· w4 (λ w5 _ → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁))
                    concl = ∀𝕎-□Func2 aw6 hyp (Mod.↑□ M ff e4)

        aw2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                              → equalInType i w2 (sub0 g₁ (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                                                    (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn ⌞ #νtestMup F f ⌟))
                                                                             (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                             (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
        aw2 w2 e2 g₁ g₂ eg =
          ≡CTerm→equalInType (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₁)) (aw3 w2 e2 g₁ g₂ eg)

        eql2 : equalInType i w1 (#PI #BAIRE
                                     (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                              (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn ⌞ #νtestMup F f ⌟))
                                                       (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                  #lam3AX
                                  #lam3AX
        eql2 = equalInType-PI
                 (λ w2 e2 → eqTypesBAIRE)
                 (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₁)) (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₂)) (ea2 w2 e2 g₁ g₂ eg))
                 aw2

        eql1 : equalInType i w1 (sub0 (#νtestMup F f)
                                      (#[0]PI #[0]BAIRE
                                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                                 #lam3AX
                                 #lam3AX
        eql1 = ≡CTerm→equalInType (sym (sub0-contQBodyPI F f (#νtestMup F f))) eql2


    h0 : ∈Type i w (#SUM #QNAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                   (#PAIR (#νtestMup F f) #lam3AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesQNAT) (equalTypes-contQBodyPI i w F F f f ∈F ∈f) (Mod.∀𝕎-□ M aw)
--}
--}

\end{code}