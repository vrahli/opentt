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
--open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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


module continuity3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                   (F : Freeze {L} W C K P G N)
                   (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
                   (CB : ChoiceBar W M C K P G X N V F E) -- TODO - We won't need everything from there: use a different module
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
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)

{--
open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)
--}

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



¬Names→updCtxt : {name : Name} {f t : Term}
                  → ¬names t ≡ true
                  → updCtxt name f t
¬Names→updCtxt {name} {f} {VAR x} nn = updCtxt-VAR _
¬Names→updCtxt {name} {f} {NAT} nn = updCtxt-NAT
¬Names→updCtxt {name} {f} {QNAT} nn = updCtxt-QNAT
¬Names→updCtxt {name} {f} {LT t t₁} nn = updCtxt-LT _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {QLT t t₁} nn = updCtxt-QLT _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {NUM x} nn = updCtxt-NUM _
¬Names→updCtxt {name} {f} {IFLT t t₁ t₂ t₃} nn = updCtxt-IFLT _ _ _ _ (¬Names→updCtxt (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (¬Names→updCtxt (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (¬Names→updCtxt (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (¬Names→updCtxt (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
¬Names→updCtxt {name} {f} {PI t t₁} nn = updCtxt-PI _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {LAMBDA t} nn = updCtxt-LAMBDA t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {APPLY t t₁} nn = updCtxt-APPLY _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {FIX t} nn = updCtxt-FIX t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {LET t t₁} nn = updCtxt-LET _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {SUM t t₁} nn = updCtxt-SUM _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {PAIR t t₁} nn = updCtxt-PAIR _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {SPREAD t t₁} nn = updCtxt-SPREAD _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {SET t t₁} nn = updCtxt-SET _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {TUNION t t₁} nn = updCtxt-TUNION _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {UNION t t₁} nn = updCtxt-UNION _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {QTUNION t t₁} nn = updCtxt-QTUNION _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {INL t} nn = updCtxt-INL t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {INR t} nn = updCtxt-INR t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {DECIDE t t₁ t₂} nn = updCtxt-DECIDE _ _ _ (¬Names→updCtxt (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (¬Names→updCtxt (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (¬Names→updCtxt (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
¬Names→updCtxt {name} {f} {EQ t t₁ t₂} nn = updCtxt-EQ _ _ _ (¬Names→updCtxt (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (¬Names→updCtxt (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (¬Names→updCtxt (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
¬Names→updCtxt {name} {f} {AX} nn = updCtxt-AX
¬Names→updCtxt {name} {f} {FREE} nn = updCtxt-FREE
¬Names→updCtxt {name} {f} {CHOOSE t t₁} nn = updCtxt-CHOOSE _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {TSQUASH t} nn = updCtxt-TSQUASH t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {TTRUNC t} nn = updCtxt-TTRUNC t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {TCONST t} nn = updCtxt-TCONST t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {SUBSING t} nn = updCtxt-SUBSING t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {DUM t} nn = updCtxt-DUM t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {FFDEFS t t₁} nn = updCtxt-FFDEFS _ _ (¬Names→updCtxt (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (¬Names→updCtxt (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
¬Names→updCtxt {name} {f} {UNIV x} nn = updCtxt-UNIV _
¬Names→updCtxt {name} {f} {LIFT t} nn = updCtxt-LIFT t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {LOWER t} nn = updCtxt-LOWER t (¬Names→updCtxt nn)
¬Names→updCtxt {name} {f} {SHRINK t} nn = updCtxt-SHRINK t (¬Names→updCtxt nn)



¬Names-APPLY-NUM : {f : Term} {m : ℕ} → ¬Names f → ¬Names (APPLY f (NUM m))
¬Names-APPLY-NUM {f} {m} nn rewrite nn = refl


false≢true : false ≡ true → ⊥
false≢true ()


getT≤ℕ-chooseT0if→ : (gc : getT-chooseT) {w : 𝕎·} {name : Name} {n m m' : ℕ}
                       → compatible· name w Res⊤
                       → getT 0 name w ≡ just (NUM m')
                       → getT≤ℕ (chooseT0if name w m' m) n name
                       → getT≤ℕ w n name
getT≤ℕ-chooseT0if→ gc {w} {name} {n} {m} {m'} compat g0 (j , h , q) with m' <? m
... | yes x rewrite gc w name m compat | sym (NUMinj (just-inj h)) = m' , g0 , ≤-trans (<⇒≤ x) q
... | no x rewrite h = j , refl , q


≡→getT≤ℕ : {w1 w2 : 𝕎·} {n : ℕ} {name : Name}
             → w1 ≡ w2
             → getT≤ℕ w1 n name
             → getT≤ℕ w2 n name
≡→getT≤ℕ {w1} {w2} {n} {name} e g rewrite e = g



{--
¬Names→isHighestℕ-step : {t u : Term} {w1 w2 : 𝕎·} {n : ℕ} {name : Name}
                           → getT≤ℕ w1 n name
                           → step t w1 ≡ just (u , w2)
                           → w1 ≡ w2 × getT≤ℕ w2 n name
¬Names→isHighestℕ-step {NAT} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {QNAT} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {LT t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {QLT t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {NUM x} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {IFLT a b c d} {u} {w1} {w2} {n} {name} gtn comp with is-NUM a
... | inj₁ (k , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with k <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {IFLT a b c d} {u} {w1} {w2} {n} {name} gtn comp | inj₁ (k , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {b} {b'} {w1} {w1'} {n} {name} gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {IFLT a b c d} {u} {w1} {w2} {n} {name} gtn comp | inj₂ p with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {PI t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {LAMBDA t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {APPLY f a} {u} {w1} {w2} {n} {name} gtn comp with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with is-CS f
... |    inj₁ (name' , p) rewrite p = ⊥-elim (false≢true nn)
... |    inj₂ y with step⊎ f w1
... |       inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {f} {f'} {w1} {w1'} {n} {name} gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {FIX f} {u} {w1} {w2} {n} {name} gtn comp with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with step⊎ f w1
... |    inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {f} {f'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {LET a f} {u} {w1} {w2} {n} {name} gtn comp with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {SUM t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {PAIR t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {SPREAD a b} {u} {w1} {w2} {n} {name} gtn comp with is-PAIR a
... | inj₁ (v₁ , v₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {SET t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {TUNION t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {UNION t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {QTUNION t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {INL t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {INR t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {DECIDE a b c} {u} {w1} {w2} {n} {name} gtn comp with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {EQ t t₁ t₂} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {AX} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {FREE} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {CHOOSE k t} {u} {w1} {w2} {n} {name} gtn comp with is-NAME k
... | inj₁ (name' , p) rewrite p = ⊥-elim (false≢true nn)
... | inj₂ x with step⊎ k w1
... |    inj₁ (k' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {k} {k'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {TSQUASH t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {TTRUNC t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {TCONST t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {SUBSING t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {DUM t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {FFDEFS t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {UNIV x} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {LIFT t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {LOWER t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {SHRINK t} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
--}


¬Names→isHighestℕ-step : {t u : Term} {w1 w2 : 𝕎·} {n : ℕ} {name : Name}
                           → ¬Names t
                           → getT≤ℕ w1 n name
                           → step t w1 ≡ just (u , w2)
                           → w1 ≡ w2 × ¬Names u × getT≤ℕ w2 n name
¬Names→isHighestℕ-step {NAT} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , refl , gtn
¬Names→isHighestℕ-step {QNAT} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , refl , gtn
¬Names→isHighestℕ-step {LT t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {QLT t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {NUM x} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , refl , gtn
¬Names→isHighestℕ-step {IFLT a b c d} {u} {w1} {w2} {n} {name} nn gtn comp with is-NUM a
... | inj₁ (k , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with k <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , ∧≡true→ₗ (¬names c) (¬names d) nn , gtn
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , ∧≡true→ᵣ (¬names c) (¬names d) nn , gtn
¬Names→isHighestℕ-step {IFLT a b c d} {u} {w1} {w2} {n} {name} nn gtn comp | inj₁ (k , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧3≡true (fst (snd ind)) (∧≡true→2-3 {¬names b} {¬names c} {¬names d} nn) (∧≡true→3-3 {¬names b} {¬names c} {¬names d} nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names b' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {b} {b'} {w1} {w1'} {n} {name} (∧≡true→1-3 {¬names b} {¬names c} {¬names d} nn) gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {IFLT a b c d} {u} {w1} {w2} {n} {name} nn gtn comp | inj₂ p with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧4≡true (proj₁ (snd ind)) (∧≡true→2-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) (∧≡true→3-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) (∧≡true→4-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} (∧≡true→1-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {PI t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {LAMBDA t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {APPLY f a} {u} {w1} {w2} {n} {name} nn gtn comp with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {a} {t} (∧≡true→ᵣ (¬names t) (¬names a) nn) (∧≡true→ₗ (¬names t) (¬names a) nn) , gtn
... | inj₂ x with is-CS f
... |    inj₁ (name' , p) rewrite p = ⊥-elim (false≢true nn)
... |    inj₂ y with step⊎ f w1
... |       inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧≡true (fst (snd ind)) (∧≡true→ᵣ (¬names f) (¬names a) nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names f' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {f} {f'} {w1} {w1'} {n} {name} (∧≡true→ₗ (¬names f) (¬names a) nn) gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {FIX f} {u} {w1} {w2} {n} {name} nn gtn comp with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {FIX (LAMBDA t)} {t} nn nn , gtn
... | inj₂ x with step⊎ f w1
... |    inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × ¬Names f' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {f} {f'} {w1} {w1'} {n} {name} nn  gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {LET a f} {u} {w1} {w2} {n} {name} nn gtn comp with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {a} {f} (∧≡true→ₗ (¬names a) (¬names f) nn) (∧≡true→ᵣ (¬names a) (¬names f) nn) , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧≡true (proj₁ (snd ind)) (∧≡true→ᵣ (¬names a) (¬names f) nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} (∧≡true→ₗ (¬names a) (¬names f) nn) gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {SUM t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {PAIR t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {SPREAD a b} {u} {w1} {w2} {n} {name} nn gtn comp with is-PAIR a
... | inj₁ (v₁ , v₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {v₂} {sub v₁ b} (∧≡true→ᵣ (¬names v₁) (¬names v₂) (∧≡true→ₗ (¬names v₁ ∧ ¬names v₂) (¬names b) nn)) (¬Names-sub {v₁} {b} (∧≡true→ₗ (¬names v₁) (¬names v₂) (∧≡true→ₗ (¬names v₁ ∧ ¬names v₂) (¬names b) nn)) (∧≡true→ᵣ (¬names v₁ ∧ ¬names v₂) (¬names b) nn)) , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧≡true (fst (snd ind)) (∧≡true→ᵣ (¬names a) (¬names b) nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} (∧≡true→ₗ (¬names a) (¬names b) nn) gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {SET t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {TUNION t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {UNION t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {QTUNION t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {INL t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {INR t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {DECIDE a b c} {u} {w1} {w2} {n} {name} nn gtn comp with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {t} {b} (∧≡true→1-3 {¬names t} {¬names b} {¬names c} nn) (∧≡true→2-3 {¬names t} {¬names b} {¬names c} nn) , gtn
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {t} {c} (∧≡true→1-3 {¬names t} {¬names b} {¬names c} nn) (∧≡true→3-3 {¬names t} {¬names b} {¬names c} nn) , gtn
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧3≡true (fst (snd ind)) (∧≡true→2-3 {¬names a} {¬names b} {¬names c} nn) (∧≡true→3-3 {¬names a} {¬names b} {¬names c} nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} (∧≡true→1-3 {¬names a} {¬names b} {¬names c} nn) gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {EQ t t₁ t₂} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {AX} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {FREE} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {CHOOSE k t} {u} {w1} {w2} {n} {name} nn gtn comp with is-NAME k
... | inj₁ (name' , p) rewrite p = ⊥-elim (false≢true nn)
... | inj₂ x with step⊎ k w1
... |    inj₁ (k' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧≡true (fst (snd ind)) (∧≡true→ᵣ (¬names k) (¬names t) nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names k' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {k} {k'} {w1} {w1'} {n} {name} (∧≡true→ₗ (¬names k) (¬names t) nn) gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {TSQUASH t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {TTRUNC t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {TCONST t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {SUBSING t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {DUM t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {FFDEFS t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {UNIV x} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {LIFT t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {LOWER t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {SHRINK t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn



¬Names→isHighestℕ : {k : ℕ} {t u : Term} {w1 w2 : 𝕎·} {n : ℕ} {name : Name}
                      → ¬Names t
                      → getT≤ℕ w1 n name
                      → (comp : steps k (t , w1) ≡ (u , w2))
                      → isHighestℕ {k} {w1} {w2} n name comp
¬Names→isHighestℕ {0} {t} {u} {w1} {w2} {n} {name} nn gtn comp
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = gtn
¬Names→isHighestℕ {suc k} {t} {u} {w1} {w2} {n} {name} nn gtn comp with step⊎ t w1
... | inj₁ (t' , w1' , z) rewrite z =
  gtn , ¬Names→isHighestℕ {k} {t'} {u} {w1'} {w2} {n} {name} (fst (snd q)) (snd (snd q)) comp
  where
    q : w1 ≡ w1' × ¬Names t' × getT≤ℕ w1' n name
    q = ¬Names→isHighestℕ-step {t} {t'} {w1} {w1'} {n} {name} nn gtn z
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = gtn




→isHighestℕ-upd-body-NUM3b :
  (gc : getT-chooseT) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → compatible· name w Res⊤
  → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , chooseT name w (NUM m))
             ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
  → getT 0 name w ≡ just (NUM m')
  → m ≤ n
  → isHighestℕ {k} {chooseT name w (NUM m)} {chooseT name w (NUM m)} n name comp
→isHighestℕ-upd-body-NUM3b gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 ltn
→isHighestℕ-upd-body-NUM3b gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftUp 0 (ct f cf) | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  g1 ,
  ¬Names→isHighestℕ {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {chooseT name w (NUM m)} {chooseT name w (NUM m)} {n} {name} (¬Names-APPLY-NUM {f} {m} nnf) g1 comp
  where
    g1 : getT≤ℕ (chooseT name w (NUM m)) n name
    g1 rewrite gc w name m compat = m , refl , ltn



→isHighestℕ-upd-body-NUM3 :
  (gc : getT-chooseT) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → compatible· name w Res⊤
  → (comp : steps k (LET (CHOOSE (NAME name) (NUM m)) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
             ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
  → getT 0 name w ≡ just (NUM m')
  → m' ≤ n
  → m ≤ n
  → isHighestℕ {k} {w} {chooseT name w (NUM m)} n name comp
→isHighestℕ-upd-body-NUM3 gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 ltn ltn'
→isHighestℕ-upd-body-NUM3 gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn ltn' =
  (m' , g0 , ltn) ,
  →isHighestℕ-upd-body-NUM3b gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn'



getT≤ℕ-chooseT→ : (gc : getT-chooseT) {name : Name} {w : 𝕎·} {n m : ℕ}
                    → compatible· name w Res⊤
                    → getT≤ℕ (chooseT name w (NUM m)) n name
                    → m ≤ n
getT≤ℕ-chooseT→ gc {name} {w} {n} {m} compat (j , e , x) rewrite gc w name m compat | NUMinj (just-inj e) = x



Σ≡justNUM≤ : {m n : ℕ} → Σ ℕ (λ j → Σ (just (NUM m) ≡ just (NUM j)) (λ x → j ≤ n)) → m ≤ n
Σ≡justNUM≤ {m} {n} (j , e , q) rewrite NUMinj (just-inj e) = q


getT-getT≤ℕ→ : {w w' : 𝕎·} {n m : ℕ} {name : Name}
                 → w ≡ w'
                 → getT 0 name w' ≡ just (NUM m)
                 → getT≤ℕ w n name
                 → m ≤ n
getT-getT≤ℕ→ {w} {w'} {n} {m} {name} eqw g (j , x , q) rewrite eqw | g | NUMinj (just-inj x) = q



→isHighestℕ-upd-body-NUM4 :
  {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
             ≡ (APPLY f (NUM m) , w))
  → getT 0 name w ≡ just (NUM m')
  → m' ≤ n
  → isHighestℕ {k} {w} {w} n name comp
→isHighestℕ-upd-body-NUM4 {0} {name} {w} {f} {n} {m} {m'} cf nnf () g0 ltn
→isHighestℕ-upd-body-NUM4 {suc k} {name} {w} {f} {n} {m} {m'} cf nnf comp g0 ltn
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  (m' , g0 , ltn) ,
  ¬Names→isHighestℕ {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {w} {w} {n} {name} (¬Names-APPLY-NUM {f} {m} nnf) (m' , g0 , ltn) comp



→isHighestℕ-upd-body-NUM2 :
  (gc : getT-chooseT) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → compatible· name w Res⊤
  → (comp : steps k (LET (IFLT (NUM m') (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
             ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
  → getT 0 name w ≡ just (NUM m')
  → m' ≤ n
  → getT≤ℕ (chooseT0if name w m' m) n name
  → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body-NUM2 gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 ltn gtn
→isHighestℕ-upd-body-NUM2 gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn gtn with m' <? m
... | yes x = (m' , g0 , ltn) , →isHighestℕ-upd-body-NUM3 gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn (getT≤ℕ-chooseT→ gc {name} {w} {n} {m} compat gtn)
... | no x = (m' , g0 , ltn) , →isHighestℕ-upd-body-NUM4 {k} {name} {w} {f} {n} {m} {m'} cf nnf comp g0 ltn



→isHighestℕ-upd-body-NUM1 : (gc : getT-chooseT) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
                             → # f
                             → ¬Names f
                             → compatible· name w Res⊤
                             → (comp : steps k (LET (IFLT (get0 name) (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
                             → getT 0 name w ≡ just (NUM m')
                             → m' ≤ n
                             → getT≤ℕ (chooseT0if name w m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body-NUM1 gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 len gtn
→isHighestℕ-upd-body-NUM1 gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn rewrite g0 =
  (m' , g0 , len) ,
  →isHighestℕ-upd-body-NUM2 gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn



→isHighestℕ-upd-body-NUM1b : (gc : getT-chooseT) {k : ℕ} {name : Name} {w w' : 𝕎·} {b f : Term} {n m m' : ℕ}
                             → # f
                             → ¬Names f
                             → compatible· name w Res⊤
                             → b ≡ NUM m
                             → w ≡ w'
                             → (comp : steps k (LET (IFLT (get0 name) (shiftDown 0 (shiftUp 0 b)) (setT name (shiftDown 0 (shiftUp 0 b))) AX)
                                                     (APPLY (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 b)) (shiftUp 0 f)))
                                                            (shiftDown 1 (shiftUp 0 (shiftUp 0 b)))) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w' m' m))
                             → getT 0 name w' ≡ just (NUM m')
                             → m' ≤ n
                             → getT≤ℕ (chooseT0if name w' m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w' m' m} n name comp
→isHighestℕ-upd-body-NUM1b gc {k} {name} {w} {w'} {b} {f} {n} {m} {m'} cf nnf compat eqb eqw comp g0 len gtn
  rewrite eqb | eqw =
  →isHighestℕ-upd-body-NUM1 gc {k} {name} {w'} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn




→isHighestℕ-upd-body-NUM : (gc : getT-chooseT) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
                             → # f
                             → ¬Names f
                             → compatible· name w Res⊤
                             → (comp : steps k (LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
                             → getT 0 name w ≡ just (NUM m')
                             → m' ≤ n
                             → getT≤ℕ (chooseT0if name w m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body-NUM gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 len gtn
→isHighestℕ-upd-body-NUM gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn =
  (m' , g0 , len) ,
  →isHighestℕ-upd-body-NUM1 gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn



→isHighestℕ-upd-body : (gc : getT-chooseT) {k1 k2 : ℕ} {name : Name} {w1 w1' : 𝕎·} {b f : Term} {n m m' : ℕ}
                         → # f
                         → ¬Names f
                         → compatible· name w1 Res⊤
                         → (comp1 : steps k1 (b , w1) ≡ (NUM m , w1'))
                         → (comp2 : steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1)
                                     ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))
                         → getT 0 name w1' ≡ just (NUM m')
                         → getT≤ℕ (chooseT0if name w1' m' m) n name
                         → isHighestℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1
                         → isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} n name comp2
→isHighestℕ-upd-body gc {0} {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf compat comp1 comp2 g0 gtn h
  rewrite pair-inj₁ comp1 | pair-inj₂ comp1 | g0 =
  →isHighestℕ-upd-body-NUM gc {k2} {name} {w1'} {f} {n} {m} {m'} cf nnf compat comp2 g0 (Σ≡justNUM≤ h) gtn
→isHighestℕ-upd-body gc {suc k1} {0} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf compat comp1 () g0 gtn h
→isHighestℕ-upd-body gc {suc k1} {suc k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf compat comp1 comp2 g0 gtn h with step⊎ b w1
... | inj₁ (b' , w' , z) rewrite z with isValue⊎ b
... |    inj₁ x
  rewrite stepVal b w1 x
        | sym (pair-inj₁ (just-inj z))
        | sym (pair-inj₂ (just-inj z)) =
  fst h , →isHighestℕ-upd-body-NUM1b gc {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf compat eqb eqw comp2 g0 (getT-getT≤ℕ→ eqw g0 (fst h)) gtn
  where
    eqb : b ≡ NUM m
    eqb = stepsVal→ₗ b (NUM m) w1 w1' k1 x comp1

    eqw : w1 ≡ w1'
    eqw = stepsVal→ᵣ b (NUM m) w1 w1' k1 x comp1
... |    inj₂ x rewrite z =
  fst h , →isHighestℕ-upd-body gc {k1} {k2} {name} {w'} {w1'} {b'} {f} {n} {m} {m'} cf nnf (⊑-compatible· (step⊑ {w1} {w'} {b} {b'} z) compat) comp1 comp2 g0 gtn (snd h)
→isHighestℕ-upd-body gc {suc k1} {suc k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf compat comp1 comp2 g0 gtn h | inj₂ z
  rewrite z | pair-inj₁ comp1 | pair-inj₂ comp1 = ⊥-elim (¬just≡nothing z)




isHighestℕ→getT≤ℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name) (comp : steps k (a , w1) ≡ (b , w2))
                       → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
                       → getT≤ℕ w1 n name
isHighestℕ→getT≤ℕ {0} {w1} {w2} {a} {b} n name comp h = h
isHighestℕ→getT≤ℕ {suc k} {w1} {w2} {a} {b} n name comp h with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = fst h
... | inj₂ z rewrite z = h



→ΣhighestUpdCtxt-upd : (gc : getT-chooseT) {name : Name} {f b : Term} {w1 : 𝕎·} {n : ℕ}
                        → compatible· name w1 Res⊤
                        → ∀𝕎-get0-NUM w1 name
                        → # f
                        → ¬Names f
                        → updCtxt name f b
                        → stepsPresHighestℕ name f (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
                        → ΣhighestUpdCtxt name f n (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
→ΣhighestUpdCtxt-upd gc {name} {f} {b} {w1} {n} compat wgt0 cf nnf nnb (k , v , w2 , comp , isv , ind) =
  k2 , APPLY f (NUM m) , chooseT0if name w1' m' m , comp2 ,
  j ,
  ¬Names→updCtxt {name} {f} {APPLY f (NUM m)} (¬Names-APPLY-NUM {f} {m} nnf)
  where
    c : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1' → Σ ℕ (λ m → Σ ℕ (λ m' →
           k1 < k
           × k2 < k
           × getT 0 name w1' ≡ just (NUM m')
           × ssteps k1 (b , w1) ≡ just (NUM m , w1')
           × steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))))))
    c = upd-decomp cf wgt0 comp isv

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

    comp1 : ssteps k1 (b , w1) ≡ just (NUM m , w1')
    comp1 = fst (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    comp1b : steps k1 (b , w1) ≡ (NUM m , w1')
    comp1b = ssteps→steps {k1} {b} {NUM m} {w1} {w1'} comp1

    comp2 : steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m)
    comp2 = snd (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    e1 : w1 ⊑· w1'
    e1 = steps→⊑ k1 b (NUM m) comp1b

    j : getT≤ℕ (chooseT0if name w1' m' m) n name → (getT≤ℕ w1 n name × isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} n name comp2)
    j g = isHighestℕ→getT≤ℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1b j1 , j2
      where
        j1 : isHighestℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1b
        j1 = ind k1 (<⇒≤ ltk1) {w1} {w1'} {b} {NUM m} {n} comp1b tt nnb (getT≤ℕ-chooseT0if→ gc {w1'} {name} {n} {m} {m'} (⊑-compatible· e1 compat) gt0 g)

        j2 : isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} {LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} n name comp2
        j2 = →isHighestℕ-upd-body gc {k1} {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf compat comp1b comp2 gt0 g j1




stepsPresHighestℕ-APPLY₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (APPLY a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-APPLY₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = APPLY→hasValue k a b v w w' comp isv



stepsPresHighestℕ-FIX₁→ : {name : Name} {f : Term} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (FIX a) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-FIX₁→ {name} {f} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = FIX→hasValue k a v w w' comp isv



stepsPresHighestℕ-LET₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (LET a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-LET₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = LET→hasValue k a b v w w' comp isv


stepsPresHighestℕ-SPREAD₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (SPREAD a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-SPREAD₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = SPREAD→hasValue k a b v w w' comp isv


stepsPresHighestℕ-DECIDE₁→ : {name : Name} {f : Term} {a b c : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (DECIDE a b c) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-DECIDE₁→ {name} {f} {a} {b} {c} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = DECIDE→hasValue k a b c v w w' comp isv



stepsPresHighestℕ-CHOOSE₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (CHOOSE a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-CHOOSE₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = CHOOSE→hasValue k a b v w w' comp isv

\end{code}
