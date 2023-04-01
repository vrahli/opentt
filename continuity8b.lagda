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


module continuity8b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

{--
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--}

open import continuity-conds(W)(C)(K)(G)(X)(N)

--open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7b2(W)(M)(C)(K)(P)(G)(X)(N)(E)



∈names-shiftNameDown-renn+→ : (name : Name) (t : Term) (w : 𝕎·)
                               → name ∈ names (shiftNameDown 0 (renn 0 (newChoiceT+ w t) t))
                               → suc name ∈ names t ⊎ name ≡ newChoiceT w t
∈names-shiftNameDown-renn+→ name t w i with name ≟ newChoiceT w t
... | yes p = inj₂ p
... | no p =
  inj₁ (∈names-shiftNameDown-renn→
          name (newChoiceT+ w t) t
          (_≤_.s≤s _≤_.z≤n)
          (λ q → p (suc-injective q))
          i)


names-sub⊆ : (a b : Term) → names (sub a b) ⊆ names a ++ names b
names-sub⊆ a b {x} i with Name∈⊎ x (names a) | Name∈⊎ x (names b)
... | inj₁ p | inj₁ q = ∈-++⁺ˡ p
... | inj₁ p | inj₂ q = ∈-++⁺ˡ p
... | inj₂ p | inj₁ q = ∈-++⁺ʳ (names a) q
... | inj₂ p | inj₂ q = ⊥-elim (¬∈names-sub {x} {a} {b} p q i)



abstract

  ¬names→[] : (a : Term) → ¬names a ≡ true → names a ≡ []
  ¬names→[] (VAR x₁) x = refl
  ¬names→[] NAT x = refl
  ¬names→[] QNAT x = refl
  ¬names→[] TNAT x = refl
  ¬names→[] (LT a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (QLT a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (NUM x₁) x = refl
  ¬names→[] (IFLT a a₁ a₂ a₃) x rewrite ¬names→[] a (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₁ (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₂ (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₃ (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) = refl
  ¬names→[] (IFEQ a a₁ a₂ a₃) x rewrite ¬names→[] a (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₁ (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₂ (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₃ (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) = refl
  ¬names→[] (SUC a) x = ¬names→[] a x
  ¬names→[] (PI a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (LAMBDA a) x = ¬names→[] a x
  ¬names→[] (APPLY a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (MSEQ s) x = refl
  ¬names→[] (MAPP s a) x = ¬names→[] a x
  ¬names→[] (FIX a) x = ¬names→[] a x
  ¬names→[] (LET a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (SUM a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (PAIR a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (SPREAD a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (WT a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (SUP a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (WREC a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (MT a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (SET a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (TUNION a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (ISECT a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (UNION a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (QTUNION a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (INL a) x = ¬names→[] a x
  ¬names→[] (INR a) x = ¬names→[] a x
  ¬names→[] (DECIDE a a₁ a₂) x rewrite ¬names→[] a (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} x) | ¬names→[] a₁ (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} x) | ¬names→[] a₂ (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} x) = refl
  ¬names→[] (EQ a a₁ a₂) x rewrite ¬names→[] a (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} x) | ¬names→[] a₁ (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} x) | ¬names→[] a₂ (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} x) = refl
  ¬names→[] (EQB a a₁ a₂ a₃) x rewrite ¬names→[] a (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₁ (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₂ (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) | ¬names→[] a₃ (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} x) = refl
  ¬names→[] AX x = refl
  ¬names→[] FREE x = refl
  ¬names→[] (CHOOSE a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] (TSQUASH a) x = ¬names→[] a x
  ¬names→[] (TTRUNC a) x = ¬names→[] a x
  ¬names→[] (TCONST a) x = ¬names→[] a x
  ¬names→[] (SUBSING a) x = ¬names→[] a x
  ¬names→[] (DUM a) x = ¬names→[] a x
  ¬names→[] (FFDEFS a a₁) x rewrite ¬names→[] a (∧≡true→ₗ (¬names a) (¬names a₁) x) | ¬names→[] a₁ (∧≡true→ᵣ (¬names a) (¬names a₁) x) = refl
  ¬names→[] PURE x = refl
  ¬names→[] (TERM a) x = ¬names→[] a x
  ¬names→[] (UNIV x₁) x = refl
  ¬names→[] (LIFT a) x = ¬names→[] a x
  ¬names→[] (LOWER a) x = ¬names→[] a x
  ¬names→[] (SHRINK a) x = ¬names→[] a x


names-WRECr⊆ : (r f : Term) (s : List Name)
                → names r ⊆ s
                → names f ⊆ s
                → names (WRECr r f) ⊆ s
names-WRECr⊆ r f s ssr ssf
  rewrite names-shiftUp 3 r
        | names-shiftUp 0 f
        | ++[] (names f)
  = ⊆++ ssf ssr


abstract

  step-pres-dom : (cc : ContConds) {a b : Term} {w1 w2 : 𝕎·}
                  → step a w1 ≡ just (b , w2)
                  → names a ⊆ dom𝕎· w1
                  → names b ⊆ dom𝕎· w2 × dom𝕎· w1 ⊆ dom𝕎· w2
  step-pres-dom cc {NAT} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {QNAT} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {TNAT} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {LT a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {QLT a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {NUM x} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {IFLT a a₁ a₂ a₃} {b} {w1} {w2} comp ss with is-NUM a
  ... | inj₁ (n , p) rewrite p with is-NUM a₁
  ... |    inj₁ (m , q) rewrite q with n <? m
  ... |       yes r rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ++⊆2→1 {names a₂} {names a₃} {dom𝕎· w1} ss , λ {x} i → i --ret c w
  ... |       no r rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ++⊆2→2 {names a₂} {names a₃} {dom𝕎· w1} ss , λ {x} i → i --ret d w
  step-pres-dom cc {IFLT a a₁ a₂ a₃} {b} {w1} {w2} comp ss | inj₁ (n , p) | inj₂ q with step⊎ a₁ w1
  ... |       inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆++ (⊆-trans (++⊆3→2 {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))
                       (⊆-trans (++⊆3→3 {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))) ,
    snd ind
    where
      ind : names a₁' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a₁} {a₁'} {w1} {w1'} z (++⊆3→1 {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss)
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {IFLT a a₁ a₂ a₃} {b} {w1} {w2} comp ss | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆++ (⊆-trans (++⊆4→2 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))
                       (⊆++ (⊆-trans (++⊆4→3 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))
                            (⊆-trans (++⊆4→4 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind)))) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆4→1 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {IFEQ a a₁ a₂ a₃} {b} {w1} {w2} comp ss with is-NUM a
  ... | inj₁ (n , p) rewrite p with is-NUM a₁
  ... |    inj₁ (m , q) rewrite q with n ≟ m
  ... |       yes r rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ++⊆2→1 {names a₂} {names a₃} {dom𝕎· w1} ss , λ {x} i → i --ret c w
  ... |       no r rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ++⊆2→2 {names a₂} {names a₃} {dom𝕎· w1} ss , λ {x} i → i --ret d w
  step-pres-dom cc {IFEQ a a₁ a₂ a₃} {b} {w1} {w2} comp ss | inj₁ (n , p) | inj₂ q with step⊎ a₁ w1
  ... |       inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆++ (⊆-trans (++⊆3→2 {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))
                       (⊆-trans (++⊆3→3 {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))) ,
    snd ind
    where
      ind : names a₁' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a₁} {a₁'} {w1} {w1'} z (++⊆3→1 {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss)
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {IFEQ a a₁ a₂ a₃} {b} {w1} {w2} comp ss | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆++ (⊆-trans (++⊆4→2 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))
                       (⊆++ (⊆-trans (++⊆4→3 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind))
                            (⊆-trans (++⊆4→4 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss) (snd ind)))) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆4→1 {names a} {names a₁} {names a₂} {names a₃} {dom𝕎· w1} ss)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {SUC a} {b} {w1} {w2} comp ss with is-NUM a
  ... | inj₁ (n , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = (λ {x} ()) , (λ {x} i → i)
  ... | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ind --ret (SUC a') w'
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z ss
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {PI a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {LAMBDA a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {APPLY a a₁} {b} {w1} {w2} comp ss with is-LAM a
  ... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    (⊆-trans (names-sub⊆ a₁ t) (⊆++ (++⊆2→2 {names t} {names a₁} {dom𝕎· w1} ss) (++⊆2→1 {names t} {names a₁} {dom𝕎· w1} ss))) ,
    (λ {x} i → i)
  ... | inj₂ x with is-CS a
  ... |    inj₁ (name , p) rewrite p with is-NUM a₁
  ... |       inj₁ (n , q) rewrite q with getT⊎ n name w1
  ... |          inj₁ (u , g) rewrite g | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ss' , λ {x} i → i
    where
      nn : ¬Names u
      nn = ContConds.ccG¬names cc n name w1 u g

      ss' : names u ⊆ dom𝕎· w1
      ss' rewrite ¬names→[] u nn = λ ()
  ... |          inj₂ g rewrite g = ⊥-elim (¬just≡nothing (sym comp)) --Data.Maybe.map (λ t → t , w) (getT n name w)
  step-pres-dom cc {APPLY a a₁} {b} {w1} {w2} comp ss | inj₂ x | inj₁ (name , p) | inj₂ y with step⊎ a₁ w1
  ... |          inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (⊆-trans (++⊆2→1 {[ name ]} {names a₁} {dom𝕎· w1} ss) (snd ind)) (fst ind) ,
    snd ind --ret (APPLY (CS name) u) w'
    where
      ind : names a₁' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a₁} {a₁'} {w1} {w1'} z (++⊆2→2 {[ name ]} {names a₁} {dom𝕎· w1} ss)
  ... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {APPLY a a₁} {b} {w1} {w2} comp ss | inj₂ x | inj₂ name with is-MSEQ a
  ... |   inj₁ (s , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ss , ⊆-refl
  step-pres-dom cc {APPLY a a₁} {b} {w1} {w2} comp ss | inj₂ x | inj₂ name | inj₂ q with step⊎ a w1
  ... | inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆-trans (++⊆2→2 {names a} {names a₁} {dom𝕎· w1} ss) (snd ind)) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆2→1 {names a} {names a₁} {dom𝕎· w1} ss)
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {MSEQ s} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {MAPP s a} {b} {w1} {w2} comp ss with is-NUM a
  ... | inj₁ (n , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = (λ {x} ()) , (λ {x} i → i)
  ... | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ind --ret (SUC a') w'
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z ss
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {FIX a} {b} {w1} {w2} comp ss with is-LAM a
  ... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆-trans (names-sub⊆ (FIX (LAMBDA t)) t) (⊆++ ss ss) , (λ {x} i → i)
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ind --ret (FIX g) w'
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z ss
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {LET a a₁} {b} {w1} {w2} comp ss with isValue⊎ a
  ... | inj₁ x rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆-trans (names-sub⊆ a a₁) ss , λ {x} i → i
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆-trans (++⊆2→2 {names a} {names a₁} {dom𝕎· w1} ss) (snd ind)) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆2→1 {names a} {names a₁} {dom𝕎· w1} ss)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {SUM a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {PAIR a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {SPREAD a a₁} {b} {w1} {w2} comp ss with is-PAIR a
  ... | inj₁ (u , v , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆-trans (names-sub⊆ v (sub u a₁)) (⊆++ (++⊆2→2 {names u} {names v} {dom𝕎· w1} (++⊆2→1 {names u ++ names v} {names a₁} {dom𝕎· w1} ss))
                                           (⊆-trans (names-sub⊆ u a₁) (⊆++ (++⊆2→1 {names u} {names v} {dom𝕎· w1} (++⊆2→1 {names u ++ names v} {names a₁} {dom𝕎· w1} ss))
                                                                           (++⊆2→2 {names u ++ names v} {names a₁} {dom𝕎· w1} ss)))) ,
    (λ {x} i → i)
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆-trans (++⊆2→2 {names a} {names a₁} {dom𝕎· w1} ss) (snd ind)) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆2→1 {names a} {names a₁} {dom𝕎· w1} ss)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {WT a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {SUP a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {WREC a a₁} {b} {w1} {w2} comp ss with is-SUP a
  ... | inj₁ (u , v , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆-trans
      (names-sub⊆ (WRECr a₁ v) (sub v (sub u a₁)))
      (⊆++
        (names-WRECr⊆
          a₁ v (dom𝕎· w1)
          (++⊆2→2 {names u ++ names v} {names a₁} {dom𝕎· w1} ss)
          (++⊆2→2 {names u} {names v} {dom𝕎· w1} (++⊆2→1 {names u ++ names v} {names a₁} {dom𝕎· w1} ss)))
        (⊆-trans
          (names-sub⊆ v (sub u a₁))
          (⊆++ (++⊆2→2 {names u} {names v} {dom𝕎· w1} (++⊆2→1 {names u ++ names v} {names a₁} {dom𝕎· w1} ss))
                (⊆-trans (names-sub⊆ u a₁)
                          (⊆++ (++⊆2→1 {names u} {names v} {dom𝕎· w1} (++⊆2→1 {names u ++ names v} {names a₁} {dom𝕎· w1} ss))
                                (++⊆2→2 {names u ++ names v} {names a₁} {dom𝕎· w1} ss)))))) ,
    (λ {x} i → i)
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆-trans (++⊆2→2 {names a} {names a₁} {dom𝕎· w1} ss) (snd ind)) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆2→1 {names a} {names a₁} {dom𝕎· w1} ss)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {MT a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {SET a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {TUNION a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {ISECT a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {UNION a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {QTUNION a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {INL a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {INR a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {DECIDE a a₁ a₂} {b} {w1} {w2} comp ss with is-INL a
  ... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆-trans (names-sub⊆ t a₁) (⊆++ (++⊆2→1 {names t} {names a₁ ++ names a₂} {dom𝕎· w1} ss)
                                   (++⊆2→1 {names a₁} {names a₂} {dom𝕎· w1} (++⊆2→2 {names t} {names a₁ ++ names a₂} {dom𝕎· w1} ss))) ,
    λ {x} i → i
  ... | inj₂ x with is-INR a
  ... |    inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆-trans (names-sub⊆ t a₂) (⊆++ (++⊆2→1 {names t} {names a₁ ++ names a₂} {dom𝕎· w1} ss)
                                   (++⊆2→2 {names a₁} {names a₂} {dom𝕎· w1} (++⊆2→2 {names t} {names a₁ ++ names a₂} {dom𝕎· w1} ss))) ,
    λ {x} i → i
  ... |    inj₂ y with step⊎ a w1
  ... |       inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆++ (⊆-trans (++⊆3→2 {names a} {names a₁} {names a₂} {dom𝕎· w1} ss) (snd ind))
                       (⊆-trans (++⊆3→3 {names a} {names a₁} {names a₂} {dom𝕎· w1} ss) (snd ind))) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆3→1 {names a} {names a₁} {names a₂} {dom𝕎· w1} ss)
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {EQ a a₁ a₂} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {EQB a a₁ a₂ a₃} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {AX} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {FREE} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {CS x} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {NAME x} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {FRESH a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ss1 , ss2
    where
      ss1 : names (shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a)) ⊆ dom𝕎· (startNewChoiceT Res⊤ w1 a)
      ss1 {x} i with ∈names-shiftNameDown-renn+→ x a w1 i
      ... | inj₁ p = dom𝕎-startNewChoiceT cc x w1 a j
        where
          j : x ∈ dom𝕎· w1
          j = ss {x} (suc→∈lowerNames {x} {names a} p)
      ... | inj₂ p rewrite p = newChoiceT∈dom𝕎 cc w1 a

      ss2 : dom𝕎· w1 ⊆ dom𝕎· (startNewChoiceT Res⊤ w1 a)
      ss2 {x} i = dom𝕎-startNewChoiceT cc x w1 a i
  step-pres-dom cc {LOAD a} {b} {w1} {w2} comp ss
    rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    (λ ()) , ⊆dom𝕎-startNewChoicesL cc w1 a (names a)
  step-pres-dom cc {CHOOSE a a₁} {b} {w1} {w2} comp ss with is-NAME a
  ... | inj₁ (name , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    (λ {x} ()) , (λ {x} i → dom𝕎-chooseT cc x name w1 a₁ i)
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    ⊆++ (fst ind) (⊆-trans (++⊆2→2 {names a} {names a₁} {dom𝕎· w1} ss) (snd ind)) ,
    snd ind
    where
      ind : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      ind = step-pres-dom cc {a} {a'} {w1} {w1'} z (++⊆2→1 {names a} {names a₁} {dom𝕎· w1} ss)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-pres-dom cc {TSQUASH a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {TTRUNC a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {TCONST a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {SUBSING a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {DUM a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {FFDEFS a a₁} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {PURE} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {TERM a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {UNIV x} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {LIFT a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {LOWER a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x
  step-pres-dom cc {SHRINK a} {b} {w1} {w2} comp ss rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ss , λ x → x



abstract
  steps-pres-dom : (cc : ContConds) {a b : Term} {w1 w2 : 𝕎·} {k : ℕ}
                   → steps k (a , w1) ≡ (b , w2)
                   → names a ⊆ dom𝕎· w1
                   → names b ⊆ dom𝕎· w2 × dom𝕎· w1 ⊆ dom𝕎· w2
  steps-pres-dom cc {a} {b} {w1} {w2} {0} comp ss rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ss , λ {x} i → i
  steps-pres-dom cc {a} {b} {w1} {w2} {suc k} comp ss with step⊎ a w1
  ... | inj₁ (a' , w1' , z) rewrite z = fst h2 , ⊆-trans (snd h1) (snd h2)
    where
      h1 : names a' ⊆ dom𝕎· w1' × dom𝕎· w1 ⊆ dom𝕎· w1'
      h1 = step-pres-dom cc {a} {a'} {w1} {w1'} z ss

      h2 : names b ⊆ dom𝕎· w2 × dom𝕎· w1' ⊆ dom𝕎· w2
      h2 = steps-pres-dom cc {a'} {b} {w1'} {w2} {k} comp (fst h1)
  ... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ss , λ {x} i → i



subRen-trans-names : {l1 l2 k1 k2 : List Name} {r1 r2 r3 : ren}
                     → l1 ⊆ k1
                     → l2 ⊆ k2
                     → subRen l1 l2 r1 r2
                     → subRen k1 k2 r2 r3
                     → subRen l1 l2 r1 r3
subRen-trans-names {l1} {l2} {k1} {k2} {r1} {r2} {.r2} ss1 ss2 sr1 (subRen-refl .r2) = sr1
subRen-trans-names {l1} {l2} {k1} {k2} {r1} {r2} {.((a , b) ∷ r3)} ss1 ss2 sr1 (subRen-trans a b .r2 r3 x x₁ sr2) =
  subRen-trans a b r1 r3 (λ z → x (ss1 {a} z)) (λ z → x₁ (ss2 {b} z)) (subRen-trans-names {l1} {l2} {k1} {k2} {r1} {r2} {r3} ss1 ss2 sr1 sr2)



abstract
  steps-updRel2-aux : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
                   → ¬ name ∈ names f
--                   → ¬ name ∈ names g
                   → # f
                   → # g
                   → (k : ℕ)
                   → (ind : (k' : ℕ) → k' < k → presUpdRel2 n name f g k')
                   → presUpdRel2 n name f g k
  steps-updRel2-aux cc gc {n} {name} {f} {g} nnf cf cg 0 ind {a} {b} {v} {w0} {w1} {w2} {w} {r} ur naid nbid niw upw compat compat' wgt0 ew01 ew0 eqw comp ish inw isv
    rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) =
    0 , b , w , r , refl , ur , upw , subRen-refl r
  steps-updRel2-aux cc gc {n} {name} {f} {g} nnf cf cg (suc k) ind {a} {b} {v} {w0} {w1} {w2} {w} {r} ur naid nbid niw upw compat compat' wgt0 ew01 ew0 eqw comp ish inw isv
    with step⊎ a w1
  ... | inj₁ (a' , w1' , z) rewrite z =
    k2 + k4 , v' , w'' , r'' ,
    steps-trans+ {k2} {k4} {b} {y2} {v'} {w} {w'} {w''} comp2 comp4 ,
    ur'' , upw'' ,
    subRen-trans-names
      {dom𝕎· w1} {dom𝕎· w} {dom𝕎· w3} {dom𝕎· w'} {r} {r'} {r''}
      (snd (steps-pres-dom cc {a} {y1} {w1} {w3} {suc k1} comp1' naid))
      (snd (steps-pres-dom cc {b} {y2} {w} {w'} {k2} comp2 nbid))
      sub' sub''
    where
      ind0 : (k' : ℕ) → k' < suc k → presUpdRel2 n name f g k'
      ind0 = ind

      ind1 : (k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k'
      ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

      spres : stepsPresUpdRel2 n name f g a' w1'
      spres = k , v , w2 , comp , isv , snd ish , snd (snd inw) , ind1

      s : ΣstepsUpdRel2 name f g a' w1 w1' b w r
      s = step-updRel2 cc gc {n} {name} {f} {g} {a} {b} {a'} {w0} {w1} {w1'} {w} {r} nnf cf cg naid nbid z spres ur upw (fst ish) (fst inw) (fst (snd inw)) niw compat compat' wgt0 ew01 ew0 eqw

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

      w' : 𝕎·
      w' = fst (snd (snd (snd (snd (snd s)))))

      r' : ren
      r' = fst (snd (snd (snd (snd (snd (snd s))))))

      comp1 : steps k1 (a' , w1') ≡ (y1 , w3)
      comp1 = fst (snd (snd (snd (snd (snd (snd (snd s)))))))

      comp2 : steps k2 (b , w) ≡ (y2 , w')
      comp2 = fst (snd (snd (snd (snd (snd (snd (snd (snd s))))))))

      ur' : updRel2 name f g r' y1 y2
      ur' = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd s)))))))))

      upw' : upto𝕎 name w3 w' r'
      upw' = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd s))))))))))

      sub' : subRen (dom𝕎· w1) (dom𝕎· w) r r'
      sub' = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd s))))))))))

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

      e4 : w ⊑· w'
      e4 = steps→⊑ k2 b y2 {w} {w'} comp2

      comp1' : steps (suc k1) (a , w1) ≡ (y1 , w3)
      comp1' = step-steps-trans2 {w1} {w1'} {w3} {a} {a'} {y1} {k1} z comp1

      ny1w : names y1 ⊆ dom𝕎· w3
      ny1w = fst (steps-pres-dom cc {a} {y1} {w1} {w3} {suc k1} comp1' naid)

      ny2w : names y2 ⊆ dom𝕎· w'
      ny2w = fst (steps-pres-dom cc {b} {y2} {w} {w'} {k2} comp2 nbid)

      niw' : name ∈ dom𝕎· w'
      niw' = snd (steps-pres-dom cc {b} {y2} {w} {w'} {k2} comp2 nbid) {name} niw

      c : Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w'' → Σ ren (λ r'' →
          steps k' (y2 , w') ≡ (v' , w'')
          × updRel2 name f g r'' v v'
          × upto𝕎 name w2 w'' r''
          × subRen (dom𝕎· w3) (dom𝕎· w') r' r''))))
      c = ind1 k3 ltk2 {y1} {y2} {v} {w0} {w3} {w2} {w'}
             ur' ny1w ny2w niw' upw'
             (⊑-compatible· e3 compat) (⊑-compatible· e4 compat')
             (∀𝕎-mon e3 wgt0) (⊑-trans· ew01 e3) (⊑-trans· ew0 e4)
             eqw comp3 ish' inw' isv

      k4 : ℕ
      k4 = fst c

      v' : Term
      v' = fst (snd c)

      w'' : 𝕎·
      w'' = fst (snd (snd c))

      r'' : ren
      r'' = fst (snd (snd (snd c)))

      comp4 : steps k4 (y2 , w') ≡ (v' , w'')
      comp4 = fst (snd (snd (snd (snd c))))

      ur'' : updRel2 name f g r'' v v'
      ur'' = fst (snd (snd (snd (snd (snd c)))))

      upw'' : upto𝕎 name w2 w'' r''
      upw'' = fst (snd (snd (snd (snd (snd (snd c))))))

      sub'' : subRen (dom𝕎· w3) (dom𝕎· w') r' r''
      sub'' = snd (snd (snd (snd (snd (snd (snd c))))))
  ... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal a w1 isv =
    ⊥-elim (¬just≡nothing z)

\end{code}
