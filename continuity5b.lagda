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
               → Σ ℕ (λ k' → Σ 𝕎· (λ w2' → steps k' (a , w1') ≡ (b , w2')
                   × upto𝕎 name w2 w2'
                   × ¬ name ∈ names b
                   × ¬ name ∈ names𝕎· w2
                   × name ∈ dom𝕎· w2))
steps-upto𝕎 cc name 0 a b w1 w2 w1' nna nnw idom comp upw
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , w1' , refl , upw , nna , nnw , idom
steps-upto𝕎 cc name (suc k) a b w1 w2 w1' nna nnw idom comp upw with step⊎ a w1
... | inj₁ (a' , w1x , z) rewrite z =
  suc (fst h2) , fst (snd h2) ,
  step-steps-trans {w1'} {fst h1} {fst (snd h2)} {a} {a'} {b} (fst (snd h1)) (fst (snd (snd h2))) ,
  snd (snd (snd h2))
  where
    h1 : Σ 𝕎· (λ w1x' → step a w1' ≡ just (a' , w1x')
           × upto𝕎 name w1x w1x'
           × ¬ name ∈ names a'
           × ¬ name ∈ names𝕎· w1x
           × name ∈ dom𝕎· w1x)
    h1 = step-upto𝕎 cc name a a' w1 w1x w1' nna nnw idom z upw

    h2 : Σ ℕ (λ k' → Σ 𝕎· (λ w2' → steps k' (a' , fst h1) ≡ (b , w2')
           × upto𝕎 name w2 w2'
           × ¬ name ∈ names b
           × ¬ name ∈ names𝕎· w2
           × name ∈ dom𝕎· w2))
    h2 = steps-upto𝕎 cc name k a' b w1x w2 (fst h1) (fst (snd (snd (snd h1)))) (fst (snd (snd (snd (snd h1))))) (snd (snd (snd (snd (snd h1))))) comp (fst (snd (snd h1)))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , w1' , refl , upw , nna , nnw , idom

\end{code}
