\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
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


module continuity3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G)
                   (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
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



¬Names→updCtxt : {name : Name} {f t : Term}
                  → ¬names t ≡ true
                  → updCtxt name f t
¬Names→updCtxt {name} {f} {t} nn = differ→updCtxt (differ-refl name name f t nn)



¬Names-APPLY-NUM : {f : Term} {m : ℕ} → ¬Names f → ¬Names (APPLY f (NUM m))
¬Names-APPLY-NUM {f} {m} nn rewrite nn = refl


false≢true : false ≡ true → ⊥
false≢true ()


getT≤ℕ-chooseT0if→ : (gc : get-choose-ℕ) {w : 𝕎·} {name : Name} {n m m' : ℕ}
                       → compatible· name w Res⊤
                       → getT 0 name w ≡ just (NUM m')
                       → getT≤ℕ (chooseT0if name w m' m) n name
                       → getT≤ℕ w n name
getT≤ℕ-chooseT0if→ gc {w} {name} {n} {m} {m'} compat g0 (j , h , q) with m' <? m
... | yes x rewrite gc name w m compat | sym (NUMinj (just-inj h)) = m' , g0 , ≤-trans x (<⇒≤ q)
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
¬Names→isHighestℕ-step {TNAT} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
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
¬Names→isHighestℕ-step {WT t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
¬Names→isHighestℕ-step {SUP t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
{--¬Names→isHighestℕ-step {DSUP a b} {u} {w1} {w2} {n} {name} gtn comp with is-SUP a
... | inj₁ (v₁ , v₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
¬Names→isHighestℕ-step {WREC a b} {u} {w1} {w2} {n} {name} gtn comp with is-SUP a
... | inj₁ (v₁ , v₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {MT t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
--¬Names→isHighestℕ-step {MSUP t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
{--¬Names→isHighestℕ-step {DMSUP a b} {u} {w1} {w2} {n} {name} gtn comp with is-SUP a
... | inj₁ (v₁ , v₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
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
¬Names→isHighestℕ-step {ISECT t t₁} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
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
¬Names→isHighestℕ-step {PURE} {u} {w1} {w2} {n} {name} gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , gtn
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
¬Names→isHighestℕ-step {TNAT} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , refl , gtn
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
¬Names→isHighestℕ-step {IFEQ a b c d} {u} {w1} {w2} {n} {name} nn gtn comp with is-NUM a
... | inj₁ (k , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with k ≟ m
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , ∧≡true→ₗ (¬names c) (¬names d) nn , gtn
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , ∧≡true→ᵣ (¬names c) (¬names d) nn , gtn
¬Names→isHighestℕ-step {IFEQ a b c d} {u} {w1} {w2} {n} {name} nn gtn comp | inj₁ (k , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧3≡true (fst (snd ind)) (∧≡true→2-3 {¬names b} {¬names c} {¬names d} nn) (∧≡true→3-3 {¬names b} {¬names c} {¬names d} nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names b' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {b} {b'} {w1} {w1'} {n} {name} (∧≡true→1-3 {¬names b} {¬names c} {¬names d} nn) gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {IFEQ a b c d} {u} {w1} {w2} {n} {name} nn gtn comp | inj₂ p with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧4≡true (proj₁ (snd ind)) (∧≡true→2-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) (∧≡true→3-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) (∧≡true→4-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} (∧≡true→1-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) gtn z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {SUC a} {u} {w1} {w2} {n} {name} nn gtn comp with is-NUM a
... | inj₁ (k , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ind
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} nn gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {PI t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {LAMBDA t} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {APPLY f a} {u} {w1} {w2} {n} {name} nn gtn comp with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , ¬Names-sub {a} {t} (∧≡true→ᵣ (¬names t) (¬names a) nn) (∧≡true→ₗ (¬names t) (¬names a) nn) , gtn
... | inj₂ x with is-CS f
... |    inj₁ (name' , p) rewrite p = ⊥-elim (false≢true nn)
... |    inj₂ y with is-MSEQ f
... |       inj₁ (sq , r) rewrite r | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , nn , gtn
... |       inj₂ r with step⊎ f w1
... |          inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
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
¬Names→isHighestℕ-step {WT t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {SUP t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
{--¬Names→isHighestℕ-step {DSUP a b} {u} {w1} {w2} {n} {name} nn gtn comp with is-SUP a
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
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
¬Names→isHighestℕ-step {WREC a b} {u} {w1} {w2} {n} {name} nn gtn comp with is-SUP a
... | inj₁ (v₁ , v₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl ,
  ¬Names-sub {WRECr b v₂} {sub v₂ (sub v₁ b)} (¬Names-WRECr {b} {v₂} (∧≡true→ᵣ (¬names v₁ ∧ ¬names v₂) (¬names b) nn) (∧≡true→ᵣ (¬names v₁) (¬names v₂) (∧≡true→ₗ (¬names v₁ ∧ ¬names v₂) (¬names b) nn))) (¬Names-sub {v₂} {sub v₁ b} (∧≡true→ᵣ (¬names v₁) (¬names v₂) (∧≡true→ₗ (¬names v₁ ∧ ¬names v₂) (¬names b) nn)) (¬Names-sub {v₁} {b} (∧≡true→ₗ (¬names v₁) (¬names v₂) (∧≡true→ₗ (¬names v₁ ∧ ¬names v₂) (¬names b) nn)) (∧≡true→ᵣ (¬names v₁ ∧ ¬names v₂) (¬names b) nn))) ,
  gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  →∧≡true (fst (snd ind)) (∧≡true→ᵣ (¬names a) (¬names b) nn) ,
  snd (snd ind)
  where
    ind : w1 ≡ w1' × ¬Names a' × getT≤ℕ w1' n name
    ind = ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} (∧≡true→ₗ (¬names a) (¬names b) nn) gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
¬Names→isHighestℕ-step {MT t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
--¬Names→isHighestℕ-step {MSUP t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
{--¬Names→isHighestℕ-step {DMSUP a b} {u} {w1} {w2} {n} {name} nn gtn comp with is-MSUP a
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
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
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
¬Names→isHighestℕ-step {ISECT t t₁} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
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
¬Names→isHighestℕ-step {EQB t t₁ t₂ t₃} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {AX} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {FREE} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {MSEQ x} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
¬Names→isHighestℕ-step {MAPP s a} {u} {w1} {w2} {n} {name} nn gtn comp with is-NUM a
... | inj₁ (k , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  refl , refl , gtn
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ¬Names→isHighestℕ-step {a} {a'} {w1} {w1'} {n} {name} nn gtn z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
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
¬Names→isHighestℕ-step {PURE} {u} {w1} {w2} {n} {name} nn gtn comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nn , gtn
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
  (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → compatible· name w Res⊤
  → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , chooseT name w (NUM m))
             ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
  → getT 0 name w ≡ just (NUM m')
  → m < n
  → isHighestℕ {k} {chooseT name w (NUM m)} {chooseT name w (NUM m)} n name comp
→isHighestℕ-upd-body-NUM3b gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 ltn
→isHighestℕ-upd-body-NUM3b gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftUp 0 (ct f cf) | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  g1 ,
  ¬Names→isHighestℕ {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {chooseT name w (NUM m)} {chooseT name w (NUM m)} {n} {name} (¬Names-APPLY-NUM {f} {m} nnf) g1 comp
  where
    g1 : getT≤ℕ (chooseT name w (NUM m)) n name
    g1 rewrite gc name w m compat = m , refl , ltn



→isHighestℕ-upd-body-NUM3 :
  (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → compatible· name w Res⊤
  → (comp : steps k (LET (CHOOSE (NAME name) (NUM m)) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
             ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
  → getT 0 name w ≡ just (NUM m')
  → m' < n
  → m < n
  → isHighestℕ {k} {w} {chooseT name w (NUM m)} n name comp
→isHighestℕ-upd-body-NUM3 gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 ltn ltn'
→isHighestℕ-upd-body-NUM3 gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn ltn' =
  (m' , g0 , ltn) ,
  →isHighestℕ-upd-body-NUM3b gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn'



getT≤ℕ-chooseT→ : (gc : get-choose-ℕ) {name : Name} {w : 𝕎·} {n m : ℕ}
                    → compatible· name w Res⊤
                    → getT≤ℕ (chooseT name w (NUM m)) n name
                    → m < n
getT≤ℕ-chooseT→ gc {name} {w} {n} {m} compat (j , e , x) rewrite gc name w m compat | NUMinj (just-inj e) = x



Σ≡justNUM≤ : {m n : ℕ} → Σ ℕ (λ j → Σ (just (NUM m) ≡ just (NUM j)) (λ x → j < n)) → m < n
Σ≡justNUM≤ {m} {n} (j , e , q) rewrite NUMinj (just-inj e) = q


getT-getT≤ℕ→ : {w w' : 𝕎·} {n m : ℕ} {name : Name}
                 → w ≡ w'
                 → getT 0 name w' ≡ just (NUM m)
                 → getT≤ℕ w n name
                 → m < n
getT-getT≤ℕ→ {w} {w'} {n} {m} {name} eqw g (j , x , q) rewrite eqw | g | NUMinj (just-inj x) = q



→isHighestℕ-upd-body-NUM4 :
  {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
             ≡ (APPLY f (NUM m) , w))
  → getT 0 name w ≡ just (NUM m')
  → m' < n
  → isHighestℕ {k} {w} {w} n name comp
→isHighestℕ-upd-body-NUM4 {0} {name} {w} {f} {n} {m} {m'} cf nnf () g0 ltn
→isHighestℕ-upd-body-NUM4 {suc k} {name} {w} {f} {n} {m} {m'} cf nnf comp g0 ltn
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  (m' , g0 , ltn) ,
  ¬Names→isHighestℕ {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {w} {w} {n} {name} (¬Names-APPLY-NUM {f} {m} nnf) (m' , g0 , ltn) comp



→isHighestℕ-upd-body-NUM2 :
  (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
  → # f
  → ¬Names f
  → compatible· name w Res⊤
  → (comp : steps k (LET (IFLT (NUM m') (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
             ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
  → getT 0 name w ≡ just (NUM m')
  → m' < n
  → getT≤ℕ (chooseT0if name w m' m) n name
  → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body-NUM2 gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 ltn gtn
→isHighestℕ-upd-body-NUM2 gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn gtn with m' <? m
... | yes x = (m' , g0 , ltn) , →isHighestℕ-upd-body-NUM3 gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 ltn (getT≤ℕ-chooseT→ gc {name} {w} {n} {m} compat gtn)
... | no x = (m' , g0 , ltn) , →isHighestℕ-upd-body-NUM4 {k} {name} {w} {f} {n} {m} {m'} cf nnf comp g0 ltn



→isHighestℕ-upd-body-NUM1 : (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
                             → # f
                             → ¬Names f
                             → compatible· name w Res⊤
                             → (comp : steps k (LET (IFLT (get0 name) (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
                             → getT 0 name w ≡ just (NUM m')
                             → m' < n
                             → getT≤ℕ (chooseT0if name w m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body-NUM1 gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 len gtn
→isHighestℕ-upd-body-NUM1 gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn rewrite g0 =
  (m' , g0 , len) ,
  →isHighestℕ-upd-body-NUM2 gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn



→isHighestℕ-upd-body-NUM1b : (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w w' : 𝕎·} {b f : Term} {n m m' : ℕ}
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
                             → m' < n
                             → getT≤ℕ (chooseT0if name w' m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w' m' m} n name comp
→isHighestℕ-upd-body-NUM1b gc {k} {name} {w} {w'} {b} {f} {n} {m} {m'} cf nnf compat eqb eqw comp g0 len gtn
  rewrite eqb | eqw =
  →isHighestℕ-upd-body-NUM1 gc {k} {name} {w'} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn




→isHighestℕ-upd-body-NUM : (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
                             → # f
                             → ¬Names f
                             → compatible· name w Res⊤
                             → (comp : steps k (LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
                             → getT 0 name w ≡ just (NUM m')
                             → m' < n
                             → getT≤ℕ (chooseT0if name w m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body-NUM gc {0} {name} {w} {f} {n} {m} {m'} cf nnf compat () g0 len gtn
→isHighestℕ-upd-body-NUM gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn =
  (m' , g0 , len) ,
  →isHighestℕ-upd-body-NUM1 gc {k} {name} {w} {f} {n} {m} {m'} cf nnf compat comp g0 len gtn



→isHighestℕ-upd-body : (gc : get-choose-ℕ) {k1 k2 : ℕ} {name : Name} {w1 w1' : 𝕎·} {b f : Term} {n m m' : ℕ}
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



→ΣhighestUpdCtxt-upd : (gc : get-choose-ℕ) {name : Name} {f b : Term} {w1 : 𝕎·} {n : ℕ}
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
        j1 = ind k1 (<⇒≤ ltk1) {w1} {w1'} {b} {NUM m} {n} comp1b tt nnb compat wgt0 (getT≤ℕ-chooseT0if→ gc {w1'} {name} {n} {m} {m'} (⊑-compatible· e1 compat) gt0 g)

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



stepsPresHighestℕ-MAPP₁→ : {name : Name} {f : Term} {s : 𝕊} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (MAPP s a) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-MAPP₁→ {name} {f} {s} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = MAPP→hasValue k s a v w w' comp isv



stepsPresHighestℕ-FIX₁→ : {name : Name} {f : Term} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (FIX a) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-FIX₁→ {name} {f} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = FIX→hasValue k a v w w' comp isv



stepsPresHighestℕ-SUC₁→ : {name : Name} {f : Term} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (SUC a) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-SUC₁→ {name} {f} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = SUC→hasValue k a v w w' comp isv



stepsPresHighestℕ-LET₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (LET a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-LET₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = LET→hasValue k a b v w w' comp isv



{--
stepsPresHighestℕ-DSUP₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (DSUP a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-DSUP₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = DSUP→hasValue k a b v w w' comp isv
--}


stepsPresHighestℕ-WREC₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (WREC a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-WREC₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = WREC→hasValue k a b v w w' comp isv


{--
stepsPresHighestℕ-DMSUP₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (DMSUP a b) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-DMSUP₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = DMSUP→hasValue k a b v w w' comp isv
--}


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


updCtxt-WRECr : {name : Name} {f : Term} {r g : Term} (cf : # f)
               → updCtxt name f r
               → updCtxt name f g
               → updCtxt name f (WRECr r g)
updCtxt-WRECr {name} {f} {r} {g} cf dr df =
  updCtxt-LAMBDA
    _
    (updCtxt-WREC
      _ _
      (updCtxt-APPLY _ _ (→updCtxt-shiftUp 0 cf df) (updCtxt-VAR 0))
      (→updCtxt-shiftUp 0 cf dr))


-- We also need something about the way f computes as for the proof about 'differ'
step-sat-isHighestℕ : (gc : get-choose-ℕ) {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
                       → compatible· name w1 Res⊤
                       → ∀𝕎-get0-NUM w1 name
                       → step a w1 ≡ just (b , w2)
                       → stepsPresHighestℕ name f b w2
                       → updCtxt name f a
                       → ¬Names f
                       → # f
                       --→ getT 0 name w2 ≡ just (NUM n)
                       → ΣhighestUpdCtxt name f n b w1 w2
step-sat-isHighestℕ gc {w1} {w2} {.NAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt-NAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAT , w1 , refl , (λ x → x , x) , updCtxt-NAT
step-sat-isHighestℕ gc {w1} {w2} {.QNAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt-QNAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QNAT , w1 , refl , (λ x → x , x) , updCtxt-QNAT
step-sat-isHighestℕ gc {w1} {w2} {.TNAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt-TNAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TNAT , w1 , refl , (λ x → x , x) , updCtxt-TNAT
step-sat-isHighestℕ gc {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-LT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-LT _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-QLT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QLT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-QLT _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(NUM x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-NUM x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NUM x , w1 , refl , (λ x → x , x) , updCtxt-NUM x
step-sat-isHighestℕ gc {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , c , w1 , refl , (λ x → x , x) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , d , w1 , refl , (λ x → x , x) , ctxt₃
step-sat-isHighestℕ gc {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-IFLT₂ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt name f n b₁' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-IFLT₂→ indb) ctxt₁ nnf cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-IFLT₁ ctxt₁ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-IFLT₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(IFEQ a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-IFEQ a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q with k1 ≟ k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , c , w1 , refl , (λ x → x , x) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , d , w1 , refl , (λ x → x , x) , ctxt₃
step-sat-isHighestℕ gc {w1} {w2} {.(IFEQ a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-IFEQ a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-IFEQ₂ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt name f n b₁' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-IFEQ₂→ indb) ctxt₁ nnf cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(IFEQ a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-IFEQ a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-IFEQ₁ ctxt₁ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-IFEQ₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(SUC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SUC a ctxt) nnf cf with is-NUM a
... | inj₁ (k , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NUM (suc k) , w1 , refl , (λ x → x , x) , updCtxt-NUM _
... | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-SUC₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-SUC₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-PI a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PI a b₁ , w1 , refl , (λ x → x , x) , updCtxt-PI _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-LAMBDA a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LAMBDA a , w1 , refl , (λ x → x , x) , updCtxt-LAMBDA _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(APPLY a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-APPLY a b₁ ctxt ctxt₁) nnf cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = concl d
  where
    d : updCtxt name f t ⊎ t ≡ updBody name f
    d = updCtxt-LAMBDA→ ctxt

    concl : updCtxt name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt name f n (sub b₁ t) w1 w1
    concl (inj₁ u) = 0 , sub b₁ t , w1 , refl , (λ s → s , s) , updCtxt-sub cf ctxt₁ u
    concl (inj₂ u) rewrite u = c2
      where
        indb' : stepsPresHighestℕ name f (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f b₁ cf = indb

        c1 : ΣhighestUpdCtxt name f n (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = →ΣhighestUpdCtxt-upd gc {name} {f} {b₁} {w1} {n} compat wgt0 cf nnf ctxt₁ indb'

        c2 : ΣhighestUpdCtxt name f n (sub b₁ (updBody name f)) w1 w1
        c2 rewrite sub-upd name f b₁ cf = c1
... | inj₂ x with is-CS a
... |    inj₁ (name' , p) rewrite p = ⊥-elim (updCtxt-CS→ ctxt)
... |    inj₂ p with is-MSEQ a
... |       inj₁ (sq , r) rewrite r | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , MAPP sq b₁ , w1 , refl , (λ s → s , s) , updCtxt-MAPP sq b₁ ctxt₁
... |       inj₂ r with step⊎ a w1
... |          inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-APPLY₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-APPLY₁→ indb) ctxt nnf cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(FIX a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-FIX a ctxt) nnf cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl d
  where
    d : updCtxt name f t ⊎ t ≡ updBody name f
    d = updCtxt-LAMBDA→ ctxt

    concl : updCtxt name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt name f n (sub (FIX (LAMBDA t)) t) w1 w1
    concl (inj₁ u) = 0 , sub (FIX (LAMBDA t)) t , w1 , refl , (λ s → s , s) , updCtxt-sub cf (updCtxt-FIX _ ctxt) u
    concl (inj₂ u) rewrite u = c2
      where
        indb' : stepsPresHighestℕ name f (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f (FIX (upd name f)) cf = indb

        c1 : ΣhighestUpdCtxt name f n (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = →ΣhighestUpdCtxt-upd gc {name} {f} {FIX (upd name f)} {w1} {n} compat wgt0 cf nnf (updCtxt-FIX _ updCtxt-upd) indb'

        c2 : ΣhighestUpdCtxt name f n (sub (FIX (upd name f)) (updBody name f)) w1 w1
        c2 rewrite sub-upd name f (FIX (upd name f)) cf = c1
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-FIX₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-FIX₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-LET a b₁ ctxt ctxt₁) nnf cf with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub a b₁ , w1 , refl , (λ s → s , s) , updCtxt-sub cf ctxt ctxt₁
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-LET₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-LET₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(WT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-WT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , WT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-WT _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(SUP a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SUP a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUP a b₁ , w1 , refl , (λ x → x , x) , updCtxt-SUP _ _ ctxt ctxt₁
{--step-sat-isHighestℕ gc {w1} {w2} {.(DSUP a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-DSUP a b₁ ctxt ctxt₁) nnf cf with is-SUP a
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub v (sub u b₁) , w1 , refl , (λ s → s , s) , updCtxt-sub cf (snd (updCtxt-SUP→ ctxt)) (updCtxt-sub cf (fst (updCtxt-SUP→ ctxt)) ctxt₁)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1'  , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-DSUP₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-DSUP₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
step-sat-isHighestℕ gc {w1} {w2} {.(WREC a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-WREC a b₁ ctxt ctxt₁) nnf cf with is-SUP a
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 ,
  sub (WRECr b₁ v) (sub v (sub u b₁)) ,
  w1 , refl , (λ s → s , s) ,
  updCtxt-sub cf (updCtxt-WRECr cf ctxt₁ (snd (updCtxt-SUP→ ctxt))) (updCtxt-sub cf (snd (updCtxt-SUP→ ctxt)) (updCtxt-sub cf (fst (updCtxt-SUP→ ctxt)) ctxt₁))
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1'  , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-WREC₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-WREC₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(MT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-MT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , MT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-MT _ _ ctxt ctxt₁
--step-sat-isHighestℕ gc {w1} {w2} {.(MSUP a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-MSUP a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , MSUP a b₁ , w1 , refl , (λ x → x , x) , updCtxt-MSUP _ _ ctxt ctxt₁
{--step-sat-isHighestℕ gc {w1} {w2} {.(DMSUP a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-DMSUP a b₁ ctxt ctxt₁) nnf cf with is-MSUP a
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub v (sub u b₁) , w1 , refl , (λ s → s , s) , updCtxt-sub cf (snd (updCtxt-MSUP→ ctxt)) (updCtxt-sub cf (fst (updCtxt-MSUP→ ctxt)) ctxt₁)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1'  , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-DMSUP₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-DMSUP₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
step-sat-isHighestℕ gc {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SUM a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUM a b₁ , w1 , refl , (λ x → x , x) , updCtxt-SUM _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-PAIR a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PAIR a b₁ , w1 , refl , (λ x → x , x) , updCtxt-PAIR _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SPREAD a b₁ ctxt ctxt₁) nnf cf with is-PAIR a
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub v (sub u b₁) , w1 , refl , (λ s → s , s) , updCtxt-sub cf (snd (updCtxt-PAIR→ ctxt)) (updCtxt-sub cf (fst (updCtxt-PAIR→ ctxt)) ctxt₁)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1'  , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-SPREAD₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-SPREAD₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SET a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SET a b₁ , w1 , refl , (λ x → x , x) , updCtxt-SET _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(ISECT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-ISECT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , ISECT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-ISECT _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-TUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TUNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt-TUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-UNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt-UNION _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-QTUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QTUNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt-QTUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(INL a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-INL a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INL a , w1 , refl , (λ x → x , x) , updCtxt-INL _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(INR a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-INR a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INR a , w1 , refl , (λ x → x , x) , updCtxt-INR _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf cf with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub t b₁ , w1 , refl , (λ s → s , s) , updCtxt-sub cf (updCtxt-INL→ ctxt) ctxt₁
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub t c , w1 , refl , (λ s → s , s) , updCtxt-sub cf (updCtxt-INR→ ctxt) ctxt₂
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-DECIDE₁ ctxt₁ ctxt₂ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-DECIDE₁→ indb) ctxt nnf cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , EQ a b₁ c , w1 , refl , (λ x → x , x) , updCtxt-EQ _ _ _ ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ gc {w1} {w2} {.(EQB a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-EQB a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , EQB a b₁ c d , w1 , refl , (λ x → x , x) , updCtxt-EQB _ _ _ _ ctxt ctxt₁ ctxt₂ ctxt₃
step-sat-isHighestℕ gc {w1} {w2} {.AX} {b} {n} {name} {f} compat wgt0 comp indb updCtxt-AX nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , AX , w1 , refl , (λ x → x , x) , updCtxt-AX
step-sat-isHighestℕ gc {w1} {w2} {.FREE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt-FREE nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FREE , w1 , refl , (λ x → x , x) , updCtxt-FREE
step-sat-isHighestℕ gc {w1} {w2} {.(MSEQ x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-MSEQ x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , MSEQ x , w1 , refl , (λ x → x , x) , updCtxt-MSEQ x
step-sat-isHighestℕ gc {w1} {w2} {.(MAPP s a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-MAPP s a ctxt) nnf cf with is-NUM a
... | inj₁ (k , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , NUM (s k) , w1 , refl , (λ s → s , s) , updCtxt-NUM (s k)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-MAPP₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-MAPP₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-CHOOSE a b₁ ctxt ctxt₁) nnf cf with is-NAME a
... | inj₁ (name' , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ⊥-elim (updCtxt-NAME→ ctxt)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-CHOOSE₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ gc compat wgt0 z (stepsPresHighestℕ-CHOOSE₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ gc {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-TSQUASH a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TSQUASH a , w1 , refl , (λ x → x , x) , updCtxt-TSQUASH _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-TTRUNC a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TTRUNC a , w1 , refl , (λ x → x , x) , updCtxt-TTRUNC _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-TCONST a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TCONST a , w1 , refl , (λ x → x , x) , updCtxt-TCONST _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SUBSING a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUBSING a , w1 , refl , (λ x → x , x) , updCtxt-SUBSING _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(PURE)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-PURE) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PURE , w1 , refl , (λ x → x , x) , updCtxt-PURE
step-sat-isHighestℕ gc {w1} {w2} {.(DUM a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-DUM a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , DUM a , w1 , refl , (λ x → x , x) , updCtxt-DUM _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-FFDEFS a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FFDEFS a b₁ , w1 , refl , (λ x → x , x) , updCtxt-FFDEFS _ _ ctxt ctxt₁
step-sat-isHighestℕ gc {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-UNIV x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNIV x , w1 , refl , (λ x → x , x) , updCtxt-UNIV x
step-sat-isHighestℕ gc {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-LIFT a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LIFT a , w1 , refl , (λ x → x , x) , updCtxt-LIFT _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-LOWER a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LOWER a , w1 , refl , (λ x → x , x) , updCtxt-LOWER _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt-SHRINK a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SHRINK a , w1 , refl , (λ x → x , x) , updCtxt-SHRINK _ ctxt
step-sat-isHighestℕ gc {w1} {w2} {.(upd name f)} {b} {n} {name} {f} compat wgt0 comp indb updCtxt-upd nnf cf
  rewrite stepVal (upd name f) w1 tt | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , upd name f , w1 , refl , (λ s → s , s) , updCtxt-upd
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))

{--
step-sat-isHighestℕ {w1} {w2} {.NAT} {b} {n} {name} {f} comp indb updCtxt-NAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , NAT , w1 , refl , (n , g0 , ≤-refl) , updCtxt-NAT
step-sat-isHighestℕ {w1} {w2} {.QNAT} {b} {n} {name} {f} comp indb updCtxt-QNAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-QNAT
step-sat-isHighestℕ {w1} {w2} {.TNAT} {b} {n} {name} {f} comp indb updCtxt-TNAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TNAT
step-sat-isHighestℕ {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} comp indb (updCtxt-LT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LT a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} comp indb (updCtxt-QLT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-QLT a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(NUM x)} {b} {n} {name} {f} comp indb (updCtxt-NUM x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-NUM x
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , ctxt₃
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  fst hn ,
  IFLT (NUM k1) (fst (snd (snd ind))) c d ,
  fst (snd (snd (snd ind))) ,
  fst (snd hn) ,
  snd (snd hn) ,
  updCtxt-IFLT (NUM k1) (fst (snd (snd ind))) c d ctxt (snd (snd (snd (snd (snd (snd ind)))))) ctxt₂ ctxt₃
  where
    ind : getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n b₁' w1'
    ind = step-sat-isHighestℕ z {!indb!} ctxt₁ nnf cf

    hn : Σ ℕ (λ k' → Σ (steps k' (IFLT (NUM k1) b₁' c d , w1') ≡ (IFLT (NUM k1) (fst (snd (snd ind))) c d , fst (snd (snd (snd ind)))))
                        (isHighestℕ {k'} {w1'} {fst (snd (snd (snd ind)))} {IFLT (NUM k1) b₁' c d} {IFLT (NUM k1) (fst (snd (snd ind))) c d} n name))
    hn = isHighestℕ-IFLT₂ {fst (snd ind)} {b₁'} {fst (snd (snd ind))} {w1'} {fst (snd (snd (snd ind)))} {n} {name} k1 c d (fst (snd (snd (snd (snd ind))))) (fst (snd (snd (snd (snd (snd ind))))))
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  fst hn ,
  IFLT (fst (snd (snd ind))) b₁ c d ,
  fst (snd (snd (snd ind))) ,
  fst (snd hn) ,
  snd (snd hn) ,
  updCtxt-IFLT (fst (snd (snd ind))) b₁ c d (snd (snd (snd (snd (snd (snd ind)))))) ctxt₁ ctxt₂ ctxt₃
  where
    ind : getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n a' w1'
    ind = step-sat-isHighestℕ z {!!} ctxt nnf cf

    hn : Σ ℕ (λ k' → Σ (steps k' (IFLT a' b₁ c d , w1') ≡ (IFLT (fst (snd (snd ind))) b₁ c d , fst (snd (snd (snd ind)))))
                        (isHighestℕ {k'} {w1'} {fst (snd (snd (snd ind)))} {IFLT a' b₁ c d} {IFLT (fst (snd (snd ind))) b₁ c d} n name))
    hn = isHighestℕ-IFLT₁ {fst (snd ind)} {a'} {fst (snd (snd ind))} {w1'} {fst (snd (snd (snd ind)))} {n} {name} b₁ c d (fst (snd (snd (snd (snd ind))))) (fst (snd (snd (snd (snd (snd ind))))))
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} comp indb (updCtxt-PI a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-PI a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} comp indb (updCtxt-LAMBDA a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LAMBDA a ctxt
step-sat-isHighestℕ {w1} {w2} {.(APPLY a b₁)} {b} {n} {name} {f} comp indb (updCtxt-APPLY a b₁ ctxt ctxt₁) nnf cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = concl d
  where
    d : updCtxt name f t ⊎ t ≡ updBody name f
    d = updCtxt-LAMBDA→ ctxt

    concl : updCtxt name f t ⊎ t ≡ updBody name f
            → getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n (sub b₁ t) w1
    concl (inj₁ u) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-sub cf ctxt₁ u
    concl (inj₂ u) rewrite u = c2
      where
        c1 : ΣhighestUpdCtxt name f n (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
             --updCtxt name f (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))))
        c1 = {!!}
-- This is not going to work.
-- Instead, we need to prove that b reduces to a term b' such that updCtxt name f b'
-- and that this computation satisfies isHighestℕ

        c2 : getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n (sub b₁ (updBody name f)) w1
        c2 rewrite sub-upd name f b₁ cf = (n , g0 , ≤-refl) , c1 -- 0 , _ , _ , refl , (n , g0 , ≤-refl) , c1
... | inj₂ x with is-CS a
... |    inj₁ (name' , p) rewrite p = ⊥-elim (updCtxt-CS→ ctxt)
... |    inj₂ p = {!!}
step-sat-isHighestℕ {w1} {w2} {.(FIX a)} {b} {n} {name} {f} comp indb (updCtxt-FIX a ctxt) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} comp indb (updCtxt-LET a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SUM a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SUM a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} comp indb (updCtxt-PAIR a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SPREAD a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SET a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SET a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-TUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TUNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-UNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-UNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-QTUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-QTUNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(INL a)} {b} {n} {name} {f} comp indb (updCtxt-INL a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-INL a ctxt
step-sat-isHighestℕ {w1} {w2} {.(INR a)} {b} {n} {name} {f} comp indb (updCtxt-INR a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-INR a ctxt
step-sat-isHighestℕ {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} comp indb (updCtxt-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} comp indb (updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ {w1} {w2} {.AX} {b} {n} {name} {f} comp indb updCtxt-AX nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-AX
step-sat-isHighestℕ {w1} {w2} {.FREE} {b} {n} {name} {f} comp indb updCtxt-FREE nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-FREE
step-sat-isHighestℕ {w1} {w2} {.(MSEQ x)} {b} {n} {name} {f} comp indb (updCtxt-MSEQ x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-MSEQ x
step-sat-isHighestℕ {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} comp indb (updCtxt-CHOOSE a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} comp indb (updCtxt-TSQUASH a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TSQUASH a ctxt
step-sat-isHighestℕ {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} comp indb (updCtxt-TTRUNC a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TTRUNC a ctxt
step-sat-isHighestℕ {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} comp indb (updCtxt-TCONST a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TCONST a ctxt
step-sat-isHighestℕ {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} comp indb (updCtxt-SUBSING a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SUBSING a ctxt
step-sat-isHighestℕ {w1} {w2} {.(PURE)} {b} {n} {name} {f} comp indb (updCtxt-PURE) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-PURE
step-sat-isHighestℕ {w1} {w2} {.(DUM a)} {b} {n} {name} {f} comp indb (updCtxt-DUM a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-DUM a ctxt
step-sat-isHighestℕ {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} comp indb (updCtxt-FFDEFS a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-FFDEFS a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} comp indb (updCtxt-UNIV x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-UNIV x
step-sat-isHighestℕ {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} comp indb (updCtxt-LIFT a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LIFT a ctxt
step-sat-isHighestℕ {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} comp indb (updCtxt-LOWER a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LOWER a ctxt
step-sat-isHighestℕ {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} comp indb (updCtxt-SHRINK a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SHRINK a ctxt
step-sat-isHighestℕ {w1} {w2} {.(upd name f)} {b} {n} {name} {f} comp indb updCtxt-upd nnf cf = {!!}
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))
--}



isHighestℕ→ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name)
               (comp : steps k (a , w1) ≡ (b , w2))
               → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
               → (w : 𝕎·) → w ∈ steps→𝕎s {k} {w1} {w2} {a} {b} comp → getT≤ℕ w n name
isHighestℕ→ {0} {w1} {w2} {a} {b} n name comp h w (here px) rewrite px = h
isHighestℕ→ {suc k} {w1} {w2} {a} {b} n name comp h w i with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = c i
  where
    c : w ∈ (w1 ∷ steps→𝕎s {k} {w'} {w2} {a'} {b} comp) → getT≤ℕ w n name
    c (here px) rewrite px = fst h
    c (there j) = isHighestℕ→ {k} {w'} {w2} {a'} {b} n name comp (snd h) w j
... | inj₂ z rewrite z = c i
  where
    c : w ∈ (w1 ∷ []) → getT≤ℕ w n name
    c (here px) rewrite px = h



→isHighestℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name)
               (comp : steps k (a , w1) ≡ (b , w2))
               → ((w : 𝕎·) → w ∈ steps→𝕎s {k} {w1} {w2} {a} {b} comp → getT≤ℕ w n name)
               → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
→isHighestℕ {0} {w1} {w2} {a} {b} n name comp h = h w1 (here refl)
→isHighestℕ {suc k} {w1} {w2} {a} {b} n name comp h with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = h w1 (here refl) , →isHighestℕ {k} {w'} {w2} {a'} {b} n name comp (λ w i → h w (there i))
... | inj₂ z rewrite z = h w1 (here refl)



stepsVal→ : (a b : Term) (w w' : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (b , w') → b ≡ a × w' ≡ w
stepsVal→ a b w w' n isv comp rewrite stepsVal a w n isv | pair-inj₁ comp | pair-inj₂ comp = refl , refl



val-steps→ : {w w1 w2 : 𝕎·} {a b v : Term} {n m : ℕ} (i : ℕ) (name : Name)
              → isValue v
              → (comp1 : steps m (a , w) ≡ (b , w1))
              → (comp2 : steps n (a , w) ≡ (v , w2))
              → Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
                  isHighestℕ {m} {w} {w1} {a} {b} i name comp1
                  → isHighestℕ {k} {w1} {w2} {b} {v} i name comp
                  → isHighestℕ {n} {w} {w2} {a} {v} i name comp2))
val-steps→ {w} {w1} {w2} {a} {b} {v} {n} {0} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = n , ≤-refl , comp2 , λ x y → y
val-steps→ {w} {w1} {w2} {a} {b} {v} {0} {suc m} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
        | stepVal a w isv
  = 0 , ≤-refl , ≡pair (fst (stepsVal→ a b w w1 m isv comp1)) (snd (stepsVal→ a b w w1 m isv comp1)) , λ (x1 , x2) x3 → x1
val-steps→ {w} {w1} {w2} {a} {b} {v} {suc n} {suc m} i name isv comp1 comp2 with step⊎ a w
... | inj₁ (a' , w' , z) rewrite z =
  fst q , ≤-trans (fst (snd q)) (<⇒≤ (n<1+n n)) , fst (snd (snd q)) , λ (x1 , x2) x3 → x1 , snd (snd (snd q)) x2 x3
  where
    q : Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
           isHighestℕ {m} {w'} {w1} {a'} {b} i name comp1
           → isHighestℕ {k} {w1} {w2} {b} {v} i name comp
           → isHighestℕ {n} {w'} {w2} {a'} {v} i name comp2))
    q = val-steps→ {w'} {w1} {w2} {a'} {b} {v} {n} {m} i name isv comp1 comp2
... | inj₂ z rewrite z
           | pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
           | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = 0 , _≤_.z≤n , refl , λ x y → x




-- We also need something about the way f computes as for the proof about 'differ'
steps-sat-isHighestℕ-aux : (gc : get-choose-ℕ) {name : Name} {f : Term}
                            → ¬Names f
                            → # f
                            → (k : ℕ)
                            → (ind : (k' : ℕ) → k' < k → presHighestℕ name f k')
                            → presHighestℕ name f k
steps-sat-isHighestℕ-aux gc {name} {f} nnf cf 0 ind {w1} {w2} {a} {b} {n} comp isvb ctxt compat wgt0 g0
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp)
  = g0 --n , g0 , ≤-refl
steps-sat-isHighestℕ-aux gc {name} {f} nnf cf (suc k) ind {w1} {w2} {a} {b} {n} comp isvb ctxt compat wgt0 g0 with step⊎ a w1
... | inj₁ (x , w , p) rewrite p =
  fst (ii gw') , snd (snd (snd comp2)) (snd (ii gw')) comp3
  where
    ind0 : (k' : ℕ) → k' < suc k → presHighestℕ name f k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presHighestℕ name f k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    q : ΣhighestUpdCtxt name f n x w1 w
    q = step-sat-isHighestℕ gc compat wgt0 p (k , b , w2 , comp , isvb , ind1) ctxt nnf cf

    k' : ℕ
    k' = fst q

    x' : Term
    x' = fst (snd q)

    w' : 𝕎·
    w' = fst (snd (snd q))

    comp1 : steps k' (x , w) ≡ (x' , w')
    comp1 = fst (snd (snd (snd q)))

    e1 : w1 ⊑· w
    e1 = step⊑ {w1} {w} {a} {x} p

    e2 : w ⊑· w'
    e2 = steps→⊑ k' x x' {w} {w'} comp1

    e3 : w1 ⊑· w'
    e3 = ⊑-trans· e1 e2

    ii : getT≤ℕ w' n name → (getT≤ℕ w1 n name × isHighestℕ {k'} {w} {w'} {x} {x'} n name comp1)
    ii = fst (snd (snd (snd (snd q))))

    uc : updCtxt name f x'
    uc = snd (snd (snd (snd (snd q))))

    comp2 : Σ ℕ (λ k0 → k0 ≤ k × Σ (steps k0 (x' , w') ≡ (b , w2)) (λ cmp →
                  isHighestℕ {k'} {w} {w'} {x} {x'} n name comp1
                  → isHighestℕ {k0} {w'} {w2} {x'} {b} n name cmp
                  → isHighestℕ {k} {w} {w2} {x} {b} n name comp))
    comp2 = val-steps→ {w} {w'} {w2} {x} {x'} {b} {k} {k'} n name isvb comp1 comp

    comp3 : isHighestℕ {fst comp2} {w'} {w2} {x'} {b} n name (fst (snd (snd comp2)))
    comp3 = ind1 (fst comp2) (fst (snd comp2)) {w'} {w2} {x'} {b} {n} (fst (snd (snd comp2))) isvb uc (⊑-compatible· e3 compat) (∀𝕎-mon e3 wgt0) g0

    gw' : getT≤ℕ w' n name
    gw' = isHighestℕ→getT≤ℕ {proj₁ comp2} {w'} {w2} {x'} {b} n name (proj₁ (snd (snd comp2))) comp3
... | inj₂ p rewrite p | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = g0 --n , g0 , ≤-refl



-- We also need something about the way f computes as for the proof about 'differ'
steps-sat-isHighestℕ : (gc : get-choose-ℕ) {name : Name} {f : Term} {k : ℕ}
                        → ¬Names f
                        → # f
                        → presHighestℕ name f k
steps-sat-isHighestℕ gc {name} {f} {k} nnf cf = <ℕind _ (steps-sat-isHighestℕ-aux gc {name} {f} nnf cf) k

\end{code}
