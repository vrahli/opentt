\begin{code}
{-# OPTIONS --rewriting #-}
--{-# OPTIONS +RTS -M6G -RTS #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite
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
open import Axiom.ExcludedMiddle


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


module continuity9b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                    (EM : ExcludedMiddle (lsuc(L)))
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
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity8b(W)(M)(C)(K)(P)(G)(X)(N)(E)



steps-updRel2 : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term} {k : ℕ}
               → ¬ name ∈ names f
--               → ¬ name ∈ names g
               → # f
               → # g
               → presUpdRel2 n name f g k
steps-updRel2 cc gc {n} {name} {f} {g} {k} nnf cf cg =
  <ℕind _ (steps-updRel2-aux cc gc {n} {name} {f} {g} nnf cf cg) k



→names-APPLY-upd⊆ : {F f : Term} {l : List Name} {name : Name}
                     → names F ⊆ l
                     → name ∈ l
                     → names f ⊆ l
                     → names (APPLY F (upd name f)) ⊆ l
→names-APPLY-upd⊆ {F} {f} {l} {name} i1 i2 i3 {x} i with ∈-++⁻ (names F) i
... | inj₁ p = i1 p
... | inj₂ (here px) rewrite px = i2
... | inj₂ (there (here px)) rewrite px = i2
... | inj₂ (there (there p)) rewrite names-shiftUp 0 f | ++[] (names f) = i3 p



→names-APPLY-force⊆ : {F f : Term} {l : List Name}
                     → names F ⊆ l
                     → names f ⊆ l
                     → names (APPLY F (force f)) ⊆ l
→names-APPLY-force⊆ {F} {f} {l} i1 i2 {x} i with ∈-++⁻ (names F) i
... | inj₁ p = i1 p
... | inj₂ p rewrite ++[] (names f) = i2 p


names∈ren-refl : (x : Name) (r : ren) → ¬ x ∈ renₗ r → ¬ x ∈ renᵣ r → names∈ren x x r
names∈ren-refl x [] nr1 nr2 = refl
names∈ren-refl x ((a , b) ∷ r) nr1 nr2 =
  inj₂ ((λ z → nr1 (here z)) ,
        (λ z → nr2 (here z)) ,
        names∈ren-refl x r (λ z → nr1 (there z)) λ z → nr2 (there z))


disjoint : (a b : List Name) → Set
disjoint a b = (n : Name) → n ∈ a → ¬ n ∈ b


disjoint++2→1 : (a b c : List Name) → disjoint (a ++ b) c → disjoint a c
disjoint++2→1 a b c disj n i = disj n (∈-++⁺ˡ i)


disjoint++2→2 : (a b c : List Name) → disjoint (a ++ b) c → disjoint b c
disjoint++2→2 a b c disj n i = disj n (∈-++⁺ʳ a i)


disjoint++3→1 : (a b c d : List Name) → disjoint (a ++ b ++ c) d → disjoint a d
disjoint++3→1 a b c d disj n i = disj n (∈-++⁺ˡ i)


disjoint++3→2 : (a b c d : List Name) → disjoint (a ++ b ++ c) d → disjoint b d
disjoint++3→2 a b c d disj n i = disj n (∈-++⁺ʳ a (∈-++⁺ˡ i))


disjoint++3→3 : (a b c d : List Name) → disjoint (a ++ b ++ c) d → disjoint c d
disjoint++3→3 a b c d disj n i = disj n (∈-++⁺ʳ a (∈-++⁺ʳ b i))


disjoint++4→1 : (a b c d e : List Name) → disjoint (a ++ b ++ c ++ d) e → disjoint a e
disjoint++4→1 a b c d e disj n i = disj n (∈-++⁺ˡ i)


disjoint++4→2 : (a b c d e : List Name) → disjoint (a ++ b ++ c ++ d) e → disjoint b e
disjoint++4→2 a b c d e disj n i = disj n (∈-++⁺ʳ a (∈-++⁺ˡ i))


disjoint++4→3 : (a b c d e : List Name) → disjoint (a ++ b ++ c ++ d) e → disjoint c e
disjoint++4→3 a b c d e disj n i = disj n (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ˡ i)))


disjoint++4→4 : (a b c d e : List Name) → disjoint (a ++ b ++ c ++ d) e → disjoint d e
disjoint++4→4 a b c d e disj n i = disj n (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ʳ c i)))


disjoint-lowerNames-renₗ→ : {l : List Name} {r : ren}
                            → disjoint (lowerNames l) (renₗ r)
                            → disjoint l (renₗ (sren r))
disjoint-lowerNames-renₗ→ {l} {r} disj 0 i j = ¬0∈renₗ-sren r j
disjoint-lowerNames-renₗ→ {l} {r} disj (suc n) i j =
  disj n (suc→∈lowerNames {n} {l} i) (suc∈renₗ-sren→ {n} {r} j)



disjoint-lowerNames-renᵣ→ : {l : List Name} {r : ren}
                            → disjoint (lowerNames l) (renᵣ r)
                            → disjoint l (renᵣ (sren r))
disjoint-lowerNames-renᵣ→ {l} {r} disj 0 i j = ¬0∈renᵣ-sren r j
disjoint-lowerNames-renᵣ→ {l} {r} disj (suc n) i j =
  disj n (suc→∈lowerNames {n} {l} i) (suc∈renᵣ-sren→ {n} {r} j)


-- Another version could be with (names a) in r
→updRel2-refl : {name : Name} {f g : Term} {r : ren} {a : Term}
              → ¬ name ∈ names a
              → disjoint (names a) (renₗ r)
              → disjoint (names a) (renᵣ r)
              → updRel2 name f g r a a
→updRel2-refl {name} {f} {g} {r} {VAR x} nn nr1 nr2 = updRel2-VAR x
→updRel2-refl {name} {f} {g} {r} {NAT} nn nr1 nr2 = updRel2-NAT
→updRel2-refl {name} {f} {g} {r} {QNAT} nn nr1 nr2 = updRel2-QNAT
→updRel2-refl {name} {f} {g} {r} {TNAT} nn nr1 nr2 = updRel2-TNAT
→updRel2-refl {name} {f} {g} {r} {LT a a₁} nn nr1 nr2 = updRel2-LT _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {QLT a a₁} nn nr1 nr2 = updRel2-QLT _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {NUM x} nn nr1 nr2 = updRel2-NUM x
→updRel2-refl {name} {f} {g} {r} {IFLT a a₁ a₂ a₃} nn nr1 nr2 = updRel2-IFLT _ _ _ _ _ _ _ _ (→updRel2-refl (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nn) (disjoint++4→1 (names a) (names a₁) (names a₂) (names a₃) (renₗ r) nr1) (disjoint++4→1 (names a) (names a₁) (names a₂) (names a₃) (renᵣ r) nr2)) (→updRel2-refl (¬∈++4→¬∈2 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nn) (disjoint++4→2 (names a) (names a₁) (names a₂) (names a₃) (renₗ r) nr1) (disjoint++4→2 (names a) (names a₁) (names a₂) (names a₃) (renᵣ r) nr2)) (→updRel2-refl (¬∈++4→¬∈3 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nn) (disjoint++4→3 (names a) (names a₁) (names a₂) (names a₃) (renₗ r) nr1) (disjoint++4→3 (names a) (names a₁) (names a₂) (names a₃) (renᵣ r) nr2)) (→updRel2-refl (¬∈++4→¬∈4 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nn) (disjoint++4→4 (names a) (names a₁) (names a₂) (names a₃) (renₗ r) nr1) (disjoint++4→4 (names a) (names a₁) (names a₂) (names a₃) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {SUC a} nn nr1 nr2 = updRel2-SUC _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {PI a a₁} nn nr1 nr2 = updRel2-PI _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {LAMBDA a} nn nr1 nr2 = updRel2-LAMBDA _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {APPLY a a₁} nn nr1 nr2 = updRel2-APPLY _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {FIX a} nn nr1 nr2 = updRel2-FIX _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {LET a a₁} nn nr1 nr2 = updRel2-LET _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {SUM a a₁} nn nr1 nr2 = updRel2-SUM _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {PAIR a a₁} nn nr1 nr2 = updRel2-PAIR _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {SPREAD a a₁} nn nr1 nr2 = updRel2-SPREAD _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {SET a a₁} nn nr1 nr2 = updRel2-SET _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {ISECT a a₁} nn nr1 nr2 = updRel2-ISECT _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {TUNION a a₁} nn nr1 nr2 = updRel2-TUNION _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {UNION a a₁} nn nr1 nr2 = updRel2-UNION _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {QTUNION a a₁} nn nr1 nr2 = updRel2-QTUNION _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {INL a} nn nr1 nr2 = updRel2-INL _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {INR a} nn nr1 nr2 = updRel2-INR _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {DECIDE a a₁ a₂} nn nr1 nr2 = updRel2-DECIDE _ _ _ _ _ _ (→updRel2-refl (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {name} nn) (disjoint++3→1 (names a) (names a₁) (names a₂) (renₗ r) nr1) (disjoint++3→1 (names a) (names a₁) (names a₂) (renᵣ r) nr2)) (→updRel2-refl (¬∈++3→¬∈2 {_} {_} {names a} {names a₁} {names a₂} {name} nn) (disjoint++3→2 (names a) (names a₁) (names a₂) (renₗ r) nr1) (disjoint++3→2 (names a) (names a₁) (names a₂) (renᵣ r) nr2)) (→updRel2-refl (¬∈++3→¬∈3 {_} {_} {names a} {names a₁} {names a₂} {name} nn) (disjoint++3→3 (names a) (names a₁) (names a₂) (renₗ r) nr1) (disjoint++3→3 (names a) (names a₁) (names a₂) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {EQ a a₁ a₂} nn nr1 nr2 = updRel2-EQ _ _ _ _ _ _ (→updRel2-refl (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {name} nn) (disjoint++3→1 (names a) (names a₁) (names a₂) (renₗ r) nr1) (disjoint++3→1 (names a) (names a₁) (names a₂) (renᵣ r) nr2)) (→updRel2-refl (¬∈++3→¬∈2 {_} {_} {names a} {names a₁} {names a₂} {name} nn) (disjoint++3→2 (names a) (names a₁) (names a₂) (renₗ r) nr1) (disjoint++3→2 (names a) (names a₁) (names a₂) (renᵣ r) nr2)) (→updRel2-refl (¬∈++3→¬∈3 {_} {_} {names a} {names a₁} {names a₂} {name} nn) (disjoint++3→3 (names a) (names a₁) (names a₂) (renₗ r) nr1) (disjoint++3→3 (names a) (names a₁) (names a₂) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {AX} nn nr1 nr2 = updRel2-AX
→updRel2-refl {name} {f} {g} {r} {FREE} nn nr1 nr2 = updRel2-FREE
→updRel2-refl {name} {f} {g} {r} {CS x} nn nr1 nr2 = updRel2-CS x x (λ z → nn (here (sym z))) (λ z → nn (here (sym z))) (names∈ren-refl x r (nr1 x (here refl)) (nr2 x (here refl)))
→updRel2-refl {name} {f} {g} {r} {NAME x} nn nr1 nr2 = updRel2-NAME x x (λ z → nn (here (sym z))) (λ z → nn (here (sym z))) (names∈ren-refl x r (nr1 x (here refl)) (nr2 x (here refl)))
→updRel2-refl {name} {f} {g} {r} {FRESH a} nn nr1 nr2 = updRel2-FRESH _ _ (→updRel2-refl {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {a} (λ z → nn (suc→∈lowerNames {name} {names a} z)) (disjoint-lowerNames-renₗ→ nr1) (disjoint-lowerNames-renᵣ→ nr2))
→updRel2-refl {name} {f} {g} {r} {LOAD a} nn nr1 nr2 = updRel2-LOAD _ --_ (→updRel2-refl {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {a} (λ z → nn (suc→∈lowerNames {name} {names a} z)) (disjoint-lowerNames-renₗ→ nr1) (disjoint-lowerNames-renᵣ→ nr2))
→updRel2-refl {name} {f} {g} {r} {CHOOSE a a₁} nn nr1 nr2 = updRel2-CHOOSE _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {TSQUASH a} nn nr1 nr2 = updRel2-TSQUASH _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {TTRUNC a} nn nr1 nr2 = updRel2-TTRUNC _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {TCONST a} nn nr1 nr2 = updRel2-TCONST _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {SUBSING a} nn nr1 nr2 = updRel2-SUBSING _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {DUM a} nn nr1 nr2 = updRel2-DUM _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {FFDEFS a a₁} nn nr1 nr2 = updRel2-FFDEFS _ _ _ _ (→updRel2-refl (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→1 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→1 (names a) (names a₁) (renᵣ r) nr2)) (→updRel2-refl (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} {name} nn) (disjoint++2→2 (names a) (names a₁) (renₗ r) nr1) (disjoint++2→2 (names a) (names a₁) (renᵣ r) nr2))
→updRel2-refl {name} {f} {g} {r} {PURE} nn nr1 nr2 = updRel2-PURE
→updRel2-refl {name} {f} {g} {r} {UNIV x} nn nr1 nr2 = updRel2-UNIV x
→updRel2-refl {name} {f} {g} {r} {LIFT a} nn nr1 nr2 = updRel2-LIFT _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {LOWER a} nn nr1 nr2 = updRel2-LOWER _ _ (→updRel2-refl nn nr1 nr2)
→updRel2-refl {name} {f} {g} {r} {SHRINK a} nn nr1 nr2 = updRel2-SHRINK _ _ (→updRel2-refl nn nr1 nr2)


steps-updRel2-app : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {F f g v : Term} {w0 w1 w2 w : 𝕎·} {r : ren} {k : ℕ}
                   → ¬ name ∈ names F
                   → ¬ name ∈ names f
--                   → ¬ name ∈ names g
                   → # f
                   → # g
                   → names F ⊆ dom𝕎· w1
                   → names F ⊆ dom𝕎· w
                   → name ∈ dom𝕎· w1
                   → name ∈ dom𝕎· w
                   → names f ⊆ dom𝕎· w1
                   → names g ⊆ dom𝕎· w
                   → disjoint (names F) (renₗ r)
                   → disjoint (names F) (renᵣ r)
                   → upto𝕎 name w1 w r
                   → compatible· name w1 Res⊤
                   → compatible· name w Res⊤
                   → ∀𝕎-get0-NUM w1 name
                   → w0 ⊑· w1
                   → w0 ⊑· w
                   → ∀𝕎 w0 (λ w' _ → (k : ℕ) → k < n → ⇛!sameℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                   → (comp : steps k (APPLY F (upd name f) , w1) ≡ (v , w2))
                   → isHighestℕ {k} {w1} {w2} {APPLY F (upd name f)} {v} n name comp
                   → ∈names𝕎 {k} {w1} {w2} {APPLY F (upd name f)} {v} name comp
                   → isValue v
                   → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w' → Σ ren (λ r' →
                       steps k' (APPLY F (force g) , w) ≡ (v' , w')
                       × updRel2 name f g r' v v'
                       × upto𝕎 name w2 w' r'
                       × subRen (dom𝕎· w1) (dom𝕎· w) r r'))))
steps-updRel2-app cc gc {n} {name} {F} {f} {g} {v} {w0} {w1} {w2} {w} {r} {k} nnF nnf cf cg nFiw1 nFiw idom1 idom2 nfiw ngiw disj1 disj2 upw compat1 compat2 gt0 ww1 ww eqn comp ish inw isv =
  steps-updRel2
    cc gc {n} {name} {f} {g} {k} nnf cf cg
    {APPLY F (upd name f)} {APPLY F (force g)} {v} {w0} {w1} {w2} {w} {r}
    (updRel2-APPLY F F (upd name f) (force g) (→updRel2-refl {name} {f} {g} {r} {F} nnF disj1 disj2) updRel2-upd)
    (→names-APPLY-upd⊆ {F} {f} {dom𝕎· w1} {name} nFiw1 idom1 nfiw)
    (→names-APPLY-force⊆ {F} {g} {dom𝕎· w} nFiw ngiw)
    idom2 upw compat1 compat2 gt0 ww1 ww eqn comp ish inw isv



disjoint[]ᵣ : (l : List Name) → disjoint l []
disjoint[]ᵣ l n i ()


wfRen-refl : (w : 𝕎·) → wfRen w w []
wfRen-refl w =
  mkWfRen (λ n ()) (λ n ()) tt tt


upto𝕎getT-refl : (name : Name) (w : 𝕎·) → upto𝕎getT name w w []
upto𝕎getT-refl name w n1 n2 k d1 d2 i rewrite i = refl


upto𝕎-refl : (name : Name) (w : 𝕎·) → upto𝕎 name w w []
upto𝕎-refl name w = mkUpto𝕎 (wfRen-refl w) (upto𝕎getT-refl name w)


¬Names→¬∈names : (name : Name) (a : Term) → ¬Names a → ¬ name ∈ names a
¬Names→¬∈names name a h rewrite ¬names→[] a h = λ ()


⇛-NUM≡→ : {a : Term} {k1 k2 : ℕ} {w : 𝕎·}
              → k1 ≡ k2
              → a ⇛ NUM k1 at w
              → a ⇛ NUM k2 at w
⇛-NUM≡→ {a} {k1} {k2} {w} e c rewrite e = c


→equalInType-NAT-⊑ : (kb : K□) {i : ℕ} {w1 w2 : 𝕎·} {a b : CTerm} {k : ℕ}
                      → ∈Type i w1 #NAT a
                      → ∈Type i w1 #NAT b
                      → w1 ⊑· w2
                      → a #⇓ #NUM k at w2
                      → b #⇓ #NUM k at w2
                      → equalInType i w1 #NAT a b
→equalInType-NAT-⊑ kb {i} {w1} {w2} {a} {b} {k} i1 i2 e c1 c2 =
  →equalInType-NAT i w1 a b (Mod.∀𝕎-□ M concl)
  where
    j1 : NATeq w1 a a
    j1 = kb (equalInType-NAT→ i w1 a a i1) w1 (⊑-refl· w1)

    k1 : ℕ
    k1 = fst j1

    x1 : a #⇛ #NUM k1 at w1
    x1 = fst (snd j1)

    e1 : k ≡ k1
    e1 = #NUMinj (#⇓-val-det {w2} {a} {#NUM k} {#NUM k1} tt tt c1 (lower (x1 w2 e)))

    j2 : NATeq w1 b b
    j2 = kb (equalInType-NAT→ i w1 b b i2) w1 (⊑-refl· w1)

    k2 : ℕ
    k2 = fst j2

    x2 : b #⇛ #NUM k2 at w1
    x2 = fst (snd j2)

    e2 : k ≡ k2
    e2 = #NUMinj (#⇓-val-det {w2} {b} {#NUM k} {#NUM k2} tt tt c2 (lower (x2 w2 e)))

    concl : ∀𝕎 w1 (λ w' _ → NATeq w' a b)
    concl w' e' = k , d1 , d2
      where
        d1 : a #⇛ #NUM k at w'
        d1 = ∀𝕎-mon e' (⇛-NUM≡→ {⌜ a ⌝} (sym e1) x1)

        d2 : b #⇛ #NUM k at w'
        d2 = ∀𝕎-mon e' (⇛-NUM≡→ {⌜ b ⌝} (sym e2) x2)




⇓NUM⊑→⇛ : {a : Term} {k1 k2 : ℕ} {w w' : 𝕎·}
            → w ⊑· w'
            → a ⇓ NUM k1 at w'
            → a ⇛ NUM k2 at w
            → a ⇛ NUM k1 at w
⇓NUM⊑→⇛ {a} {k1} {k2} {w} {w'} e c d =
  ⇛-NUM≡→ {a} {k2} {k1} {w} (NUMinj (⇓-val-det {w'} {a} {NUM k2} {NUM k1} tt tt c' c)) d
  where
    c' : a ⇓ NUM k2 at w'
    c' = lower (d w' e)


⇓NUM→⇛ : {a : Term} {k1 k2 : ℕ} {w : 𝕎·}
           → a ⇓ NUM k1 at w
           → a ⇛ NUM k2 at w
           → a ⇛ NUM k1 at w
⇓NUM→⇛ {a} {k1} {k2} {w} c d = ⇓NUM⊑→⇛ {a} {k1} {k2} {w} {w} (⊑-refl· w) c d



equalInType-NAT-mon-rev : (kb : K□) {i : ℕ} {w1 w2 : 𝕎·} {a b : CTerm}
                      → ∈Type i w1 #NAT a
                      → ∈Type i w1 #NAT b
                      → w1 ⊑· w2
                      → equalInType i w2 #NAT a b
                      → equalInType i w1 #NAT a b
equalInType-NAT-mon-rev kb {i} {w1} {w2} {a} {b} i1 i2 e eqn =
  →equalInType-NAT i w1 a b (Mod.∀𝕎-□ M aw)
  where
    j1 : NATeq w1 a a
    j1 = kb (equalInType-NAT→ i w1 a a i1) w1 (⊑-refl· w1)

    k1 : ℕ
    k1 = fst j1

    x1 : a #⇛ #NUM k1 at w1
    x1 = fst (snd j1)

    j2 : NATeq w1 b b
    j2 = kb (equalInType-NAT→ i w1 b b i2) w1 (⊑-refl· w1)

    k2 : ℕ
    k2 = fst j2

    x2 : b #⇛ #NUM k2 at w1
    x2 = fst (snd j2)

    j3 : NATeq w2 a b
    j3 = kb (equalInType-NAT→ i w2 a b eqn) w2 (⊑-refl· w2)

    k3 : ℕ
    k3 = fst j3

    x3 : a #⇛ #NUM k3 at w2
    x3 = fst (snd j3)

    y3 : b #⇛ #NUM k3 at w2
    y3 = snd (snd j3)

    z1 : a #⇛ #NUM k3 at w1
    z1 = ⇓NUM⊑→⇛ {⌜ a ⌝} {k3} {k1} {w1} {w2} e (lower (x3 w2 (⊑-refl· w2))) x1

    z2 : b #⇛ #NUM k3 at w1
    z2 = ⇓NUM⊑→⇛ {⌜ b ⌝} {k3} {k2} {w1} {w2} e (lower (y3 w2 (⊑-refl· w2))) x2

    aw : ∀𝕎 w1 (λ w' _ → NATeq w' a b)
    aw w' e' = k3 , ∀𝕎-mon e' z1 , ∀𝕎-mon e' z2


→→equalInType-NAT : (kb : K□) {i : ℕ} {w : 𝕎·} {a b : CTerm}
                      → ∈Type i w #NAT a
                      → ∈Type i w #NAT b
                      → ((k : ℕ) → a #⇓ #NUM k at w → b #⇓ #NUM k at w)
                      → equalInType i w #NAT a b
→→equalInType-NAT kb {i} {w} {a} {b} i1 i2 imp =
  →equalInType-NAT i w a b (Mod.∀𝕎-□ M aw)
  where
    j1 : NATeq w a a
    j1 = kb (equalInType-NAT→ i w a a i1) w (⊑-refl· w)

    k1 : ℕ
    k1 = fst j1

    x1 : a #⇛ #NUM k1 at w
    x1 = fst (snd j1)

    j2 : NATeq w b b
    j2 = kb (equalInType-NAT→ i w b b i2) w (⊑-refl· w)

    k2 : ℕ
    k2 = fst j2

    x2 : b #⇛ #NUM k2 at w
    x2 = fst (snd j2)

    y2 : b #⇓ #NUM k1 at w
    y2 = imp k1 (lower (x1 w (⊑-refl· w)))

    aw : ∀𝕎 w (λ w' _ → NATeq w' a b)
    aw w1 e1 = k1 , ∀𝕎-mon e1 x1 , ∀𝕎-mon e1 (⇓NUM→⇛ y2 x2)


∈#BAIRE→NAT→upd-force→≡ : (kb : K□) {i : ℕ} {w0 w1 w2 : 𝕎·} {F f : CTerm} {v : Term} {k : ℕ} {name : Name}
                             → ∀𝕎-get0-NUM w0 name
                             → ∈Type i w0 #BAIRE→NAT F
                             → ∈Type i w0 #BAIRE f
                             → isValue v
                             → w0 ⊑· w1
                             → w0 ⊑· w2
                             → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v at w1
                             → APPLY ⌜ F ⌝ (force ⌜ f ⌝) ⇓ NUM k at w2
                             → v ≡ NUM k
∈#BAIRE→NAT→upd-force→≡ kb {i} {w0} {w1} {w2} {F} {f} {v} {k} {name} gt0 iF if isv e1 e2 c1 c2 =
  trans (⇓-val-det {w1} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {NUM k1} isv tt c1 (lower (x1 w1 e1)))
        (sym (⇓-val-det {w2} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {NUM k} {NUM k1} tt tt c2 (lower (x2 w2 e2))))
  where
    j1 : equalInType i w0 #BAIRE (#upd name f) (#force f)
    j1 = equalInType-upd-force i w0 name f gt0 if

    j2 : equalInType i w0 #NAT (#APPLY F (#upd name f)) (#APPLY F (#force f))
    j2 = ∈BAIRE→NAT→ {i} {w0} {F} {F} {#upd name f} {#force f} iF j1

    j3 : NATeq w0 (#APPLY F (#upd name f)) (#APPLY F (#force f))
    j3 = kb (equalInType-NAT→ i w0 (#APPLY F (#upd name f)) (#APPLY F (#force f)) j2) w0 (⊑-refl· w0)

    k1 : ℕ
    k1 = fst j3

    x1 : #APPLY F (#upd name f) #⇛ #NUM k1 at w0
    x1 = fst (snd j3)

    x2 : #APPLY F (#force f) #⇛ #NUM k1 at w0
    x2 = snd (snd j3)


-- TODO: get rid of (¬ name ∈ names ⌜ g ⌝)?
-- NOTE: We can't guarantee the upto𝕎 assumption because in this case, w1s' and w1 might be different
--   extensions of the same 𝕎·
-- TODO: can't we instead derive that (APPLY F (upd name f)) computes to NUM k' in w1?
eqfgq-aux : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
            {i : ℕ} {w0 w1 w1s' w2 : 𝕎·} {F f g : CTerm} {name : Name}
            {k : ℕ} {v : Term} {j : ℕ} {tn : ℕ}
            → ¬ name ∈ names ⌜ F ⌝
            → ¬ name ∈ names ⌜ f ⌝
--            → ¬ name ∈ names ⌜ g ⌝
            → ¬ name ∈ names𝕎· w1s'
            → name ∈ dom𝕎· w1s'
            → name ∈ dom𝕎· w1
            → names ⌜ F ⌝ ⊆ dom𝕎· w1s'
            → names ⌜ F ⌝ ⊆ dom𝕎· w1
            → names ⌜ f ⌝ ⊆ dom𝕎· w1s'
            → names ⌜ g ⌝ ⊆ dom𝕎· w1
--            → names ⌜ g ⌝ ⊆ dom𝕎· w1s'
            → upto𝕎 name w1s' w1 []
            → compatible· name w1s' Res⊤
            → compatible· name w1 Res⊤
            → ∀𝕎-get0-NUM w1s' name
            → getT 0 name w2 ≡ just (NUM j)
            → tn ≡ suc j
            → isValue v
            → w0 ⊑· w1s'
            → w0 ⊑· w1
            → ∀𝕎-get0-NUM w0 name
            → ∈Type i w0 #BAIRE→NAT F
            → ∈Type i w0 #BAIRE f
            → ∀𝕎 w0 (λ w' _ → (k : ℕ) → k < tn → ⇛!sameℕ w' (APPLY ⌜ f ⌝ (NUM k)) (APPLY ⌜ g ⌝ (NUM k)))
            → steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1s') ≡ (v , w2)
            → (k' : ℕ) → #APPLY F (#force f) #⇓ #NUM k' at w1 → #APPLY F (#force g) #⇓ #NUM k' at w1
eqfgq-aux cc cn kb gc {i} {w0} {w1} {w1s'} {w2} {F} {f} {g} {name} {k} {v} {j} {tn} nnF nnf nnw1s' idomw1s' idomw1 nFiw1 nFiw2 nfiw ngiw upw compat1 compat2 wgt0 g0 eqj isvv ew1 ew2 get0 inF inf eqn compa k' c =
  ⇓-from-to→⇓ {w1} {w'} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {NUM k'} (k'' , compg2)
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

    compg0 : Σ ℕ (λ k'' → Σ Term (λ v' → Σ 𝕎· (λ w' → Σ ren (λ r' →
               steps k'' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w')
               × updRel2 name ⌜ f ⌝ ⌜ g  ⌝ r' v v'
               × upto𝕎 name w2 w' r'
               × subRen (dom𝕎· w1s') (dom𝕎· w1) [] r'))))
    compg0 = steps-updRel2-app
               cc gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {w0} {w1s'} {w2} {w1} {[]} {k}
               nnF nnf {--(¬Names→¬∈names name ⌜ g ⌝ nng)--} (CTerm.closed f) (CTerm.closed g) nFiw1 nFiw2 idomw1s' idomw1 nfiw ngiw
               (disjoint[]ᵣ (names ⌜ F ⌝)) (disjoint[]ᵣ (names ⌜ F ⌝)) upw compat1 compat2 wgt0
               ew1 ew2 eqn {--(∀𝕎-mon e1' eqb3)--} compa ish (snd pish) isvv

    k'' : ℕ
    k'' = fst compg0

    v' : Term
    v' = fst (snd compg0)

    w' : 𝕎·
    w' = fst (snd (snd compg0))

    r' : ren
    r' = fst (snd (snd (snd compg0)))

    compg1 : steps k'' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w')
    compg1 = fst (snd (snd (snd (snd compg0))))

--    compg2 : steps k'' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
--    compg2 = fst (¬Names→steps k'' w1s' w' w1 (APPLY ⌜ F ⌝ (force ⌜ g ⌝)) v' {!!} compg1)

    -- we can prove that v ≡ NUM k' from compa and c, and therefore that v' ≡ NUM k' from ur
    ur :  updRel2 name ⌜ f ⌝ ⌜ g  ⌝ r' v v'
    ur = fst (snd (snd (snd (snd (snd compg0)))))

    eqv : v ≡ NUM k'
    eqv = ∈#BAIRE→NAT→upd-force→≡
            kb {i} {w0} {w1s'} {w1} {F} {f} {v} {k'} {name} get0 inF inf isvv ew1 ew2
            (⇓-from-to→⇓ {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} (k , compa)) c

    ur' :  updRel2 name ⌜ f ⌝ ⌜ g  ⌝ r' (NUM k') v'
    ur' rewrite sym eqv = ur

    eqv' : v' ≡ NUM k'
    eqv' = updRel2-NUMₗ→ ur'

    compg2 : steps k'' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (NUM k' , w')
    compg2 rewrite (sym eqv') = compg1

{--
    equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
    equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

    compg : #APPLY F (#force g) #⇓ #NUM n at w1
    compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}



QBAIREn! : Term → Term
QBAIREn! n = FUN (QNATn n) NAT!


#QBAIREn! : CTerm → CTerm
#QBAIREn! n = ct (QBAIREn! ⌜ n ⌝) c
  where
    c : # QBAIREn! ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n



≡QBAIREn! : (n : CTerm) → #QBAIREn! n ≡ #FUN (#QNATn n) #NAT!
≡QBAIREn! n = CTerm≡ refl


νtestML-QNAT-shift : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → #⇓sameℕ w (#νtestMLup F f) (#νtestMLup F f)
νtestML-QNAT-shift cn kb gc i w F f ∈F ∈f =
  fst smn , ack , ack
  where
    tM : Term
    tM = testMLup 0 ⌜ F ⌝ ⌜ f ⌝

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : νtestMLup ⌜ F ⌝ ⌜ f ⌝ ⇓ testML name ⌜ F ⌝ ⌜ f ⌝ from w to w1
    s1 = 1 , ≡pair (shiftNameDown-renn-shiftNameUp-LOAD name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

    smn : #⇓sameℕ w1 (#testML name F f) (#testML name F f)
    smn = testML-QNAT-shift cn kb gc i w1 F f name comp1 (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

    ack : νtestMLup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (fst smn) at w
    ack = ⇓-trans₁ {w} {w1} {νtestMLup ⌜ F ⌝ ⌜ f ⌝} {testML name ⌜ F ⌝ ⌜ f ⌝} {NUM (proj₁ smn)} s1 (fst (snd smn))



testML-QNAT : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
              (i : ℕ) (w : 𝕎·) (F f : CTerm)
              → ∈Type i w #BAIRE→NAT F
              → ∈Type i w #BAIRE f
              → ∈Type i w #QNAT (#νtestMLup F f)
testML-QNAT cn kb gc i w F f ∈F ∈f =
  →equalInType-QNAT i w (#νtestMLup F f) (#νtestMLup F f) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → #weakMonEq w' (#νtestMLup F f) (#νtestMLup F f))
    aw w1 e1 w2 e2 = lift (νtestML-QNAT-shift cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))





names𝕎-startNewChoices→ : (cc : ContConds) (w : 𝕎·) (t : Term) (name : Name)
                          → name ∈ names𝕎· (startNewChoices Res⊤ w t)
                          → name ∈ names𝕎· w
names𝕎-startNewChoices→ cc w t name i rewrite names𝕎-startNewChoices cc w t = i



names⊆dom𝕎-startNewChoicesL : (cc : ContConds) (w : 𝕎·) (t : Term) (l : List Name)
                               → l ⊆ dom𝕎· (startNewChoicesL Res⊤ w t l)
names⊆dom𝕎-startNewChoicesL cc w t [] {x} ()
names⊆dom𝕎-startNewChoicesL cc w t (n ∷ l) {x} (here px) rewrite px with Name∈⊎ n (dom𝕎· w)
... | inj₁ p = ⊆dom𝕎-startNewChoicesL cc (startNewChoiceT Res⊤ w t) t l (dom𝕎-startNewChoiceT cc n w t p)
... | inj₂ p = ⊆dom𝕎-startNewChoicesL cc (startChoice· n Res⊤ w) t l (ContConds.ccNchoice cc w n p)
names⊆dom𝕎-startNewChoicesL cc w t (n ∷ l) {x} (there px) with Name∈⊎ n (dom𝕎· w)
... | inj₁ p = names⊆dom𝕎-startNewChoicesL cc (startNewChoiceT Res⊤ w t) t l px
... | inj₂ p = names⊆dom𝕎-startNewChoicesL cc (startChoice· n Res⊤ w) t l px


names⊆dom𝕎-startNewChoices : (cc : ContConds) (w : 𝕎·) (t : Term)
                              → names t ⊆ dom𝕎· (startNewChoices Res⊤ w t)
names⊆dom𝕎-startNewChoices cc w t = names⊆dom𝕎-startNewChoicesL cc w t (names t)



νtestML⇓→step' : {F f v : Term} {w1 w2 : 𝕎·}
                → # F
                → # f
                → isValue v
                → νtestMLup F f ⇓ v from w1 to w2
                → testML (newChoiceT w1 (testMLup 0 F f)) F f ⇓ v from startNewChoiceT Res⊤ w1 (testMLup 0 F f) to w2
νtestML⇓→step' {F} {f} {v} {w1} {w2} cF cf isv (0 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
νtestML⇓→step' {F} {f} {v} {w1} {w2} cF cf isv (suc k , comp)
  rewrite shiftNameDown-renn-shiftNameUp-LOAD (newChoiceT w1 (testMLup 0 F f)) F f cF cf
  = k , comp



abstract
  νtestML⇓→ : (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ}
             → # F
             → # f
             → νtestMLup F f ⇓ NUM n from w1 to w2
             → Σ Term (λ v → Σ ℕ (λ k →
                 APPLY F (upd (newChoiceT w1 (testMLup 0 F f)) f) ⇓ v from (chooseT (newChoiceT w1 (testMLup 0 F f)) (startNewChoices Res⊤ (startNewChoiceT Res⊤ w1 (testMLup 0 F f)) F) (NUM 0)) to w2
                 × isValue v
                 × getT 0 (newChoiceT w1 (testMLup 0 F f)) w2 ≡ just (NUM k)
                 × n ≡ suc k
                 × compatible· (newChoiceT w1 (testMLup 0 F f)) (startNewChoiceT Res⊤ w1 (testMLup 0 F f)) Res⊤))
  νtestML⇓→ cn {w1} {w2} {F} {f} {n} cF cf comp =
    fst comp3 ,
    fst (snd comp3) ,
    fst (snd (snd comp3)) ,
    fst (snd (snd (snd comp3))) ,
    fst (snd (snd (snd (snd comp3)))) ,
    snd (snd (snd (snd (snd comp3)))) ,
    compat1
    where
      name : Name
      name = newChoiceT w1 (testMLup 0 F f)

      w1' : 𝕎·
      w1' = startNewChoiceT Res⊤ w1 (testMLup 0 F f)

      comp1 : testML name F f ⇓ NUM n from w1' to w2
      comp1 = νtestML⇓→step' cF cf tt comp

      compat1 : compatible· name w1' Res⊤
      compat1 = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testMLup 0 F f))

      comp3 : Σ Term (λ v → Σ ℕ (λ k →
                APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoices Res⊤ w1' F) (NUM 0)) to w2
                × isValue v
                × getT 0 name w2 ≡ just (NUM k)
                × n ≡ suc k))
      comp3 = testML⇓→ cn {w1'} {w2} {F} {f} {n} {name} cF cf compat1 comp1




eqfgq : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
        {i : ℕ} {w : 𝕎·} {F f g : CTerm}
        → #¬Names g
        → (∈F : ∈Type i w #BAIRE→NAT F)
        → (∈f : ∈Type i w #BAIRE f)
        → ∈Type i w #BAIRE g
        → smallestMod cn kb gc i w F f ∈F ∈f
        → equalInType i w (#QBAIREn! (#νtestMLup F f)) f g
--       ((n : ℕ) → n < ? → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
        → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
eqfgq cc cn kb gc {i} {w} {F} {f} {g} nng ∈F ∈f ∈g smod eqb =
  equalInType-trans (equalInType-APPLY-force ∈F ∈f) (equalInType-trans eqf (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
  where
    eqb1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#QNATn (#νtestMLup F f)) a₁ a₂
                         → equalInType i w' #NAT! (#APPLY f a₁) (#APPLY g a₂))
    eqb1 = equalInType-FUN→ (≡CTerm→equalInType (≡QBAIREn! (#νtestMLup F f)) eqb)

    eqb2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                         → □· w' (λ w'' _ → Σ ℕ (λ tn → Σ ℕ (λ k → #νtestMLup F f #⇓ #NUM tn at w'' × a₁ #⇛ #NUM k at w'' × a₂ #⇛ #NUM k at w'' × k < tn)))
                         → □· w' (λ w'' _ → #⇛!sameℕ w'' (#APPLY f a₁) (#APPLY g a₂)))
    eqb2 w1 e1 a₁ a₂ eqa = equalInType-NAT!→ i w1 (#APPLY f a₁) (#APPLY g a₂) (eqb1 w1 e1 a₁ a₂ (→equalInType-QNATn (testML-QNAT cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)) eqa))

-- NOTE: It is not clear how this could work since to prove compg0 below we need to know that f and g
-- compute to the same number on the same input, as long as this input is less than the modulus
-- of F at f. However, to use eqb2 for that we would have to prove that this input is less than
-- all possible moduli of continuity for all extensions...
-- Counter-example?

    eqb3 : ∀𝕎 w (λ w' _ → (k : ℕ)
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMLup F f #⇓ #NUM n at w'' × k < n)))
                         → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb3 w1 e1 k comp = kb z w1 (⊑-refl· _)
      where
        z : □· w1 (λ w'' _ → #⇛!sameℕ w'' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
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

    w1' : 𝕎·
    w1' = fst smod

    e1' : w ⊑· w1'
    e1' = fst (snd smod)

    sma : smallestModAux cn kb gc i w F f w1' e1' ∈F ∈f
    sma = snd (snd smod)

    eqb4 : Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMLup F f #⇓ #NUM n from w1' to w2
                     × ∀𝕎 w1' (λ w' _ → (k : ℕ) → k < n
                                       → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
    eqb4 = smallestModAux→⇛!sameℕ cn kb gc {i} {w} {F} {f} {g} {w1'} {e1'} ∈F ∈f sma eqb3

    tn : ℕ
    tn = fst eqb4

    w2 : 𝕎·
    w2 = fst (snd eqb4)

    compt : νtestMLup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1' to w2
    compt = fst (snd (snd eqb4))

    eqb5 : ∀𝕎 w1' (λ w' _ → (k : ℕ) → k < tn
                           → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb5 = snd (snd (snd eqb4))

    w1s : 𝕎·
    w1s = startNewChoiceT Res⊤ w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)

    w1l : 𝕎·
    w1l = startNewChoices Res⊤ w1s ⌜ F ⌝

    name : Name
    name = newChoiceT w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)

    w1s' : 𝕎·
    w1s' = chooseT name w1l (NUM 0)

    nFw1s' : names ⌜ F ⌝ ⊆ dom𝕎· w1s'
    nFw1s' {x} i = dom𝕎-chooseT cc x name w1l (NUM 0) (names⊆dom𝕎-startNewChoices cc w1s ⌜ F ⌝ i)

    compu : Σ Term (λ v → Σ ℕ (λ j →
               APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v from w1s' to w2
               × isValue v
               × getT 0 name w2 ≡ just (NUM j)
               × tn ≡ suc j
               × compatible· name w1s Res⊤))
    compu = νtestML⇓→ cn {w1'} {w2} {⌜ F ⌝} {⌜ f ⌝} {tn} (CTerm.closed F) (CTerm.closed f) compt

    v : Term
    v = fst compu

    j : ℕ
    j = fst (snd compu)

    e0' : w1' ⊑· w1s'
    e0' = ⊑-trans· (startNewChoiceT⊏ Res⊤ w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝))
                   (⊑-trans· (startNewChoices⊑ Res⊤ (startNewChoiceT Res⊤ w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)) ⌜ F ⌝)
                             (choose⊑· name w1l (T→ℂ· (NUM 0))))

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

    compatl : compatible· name w1l Res⊤
    compatl = ⊑-compatible· (startNewChoices⊑ Res⊤ (startNewChoiceT Res⊤ w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)) ⌜ F ⌝) compat

    compat1 : compatible· name w1s' Res⊤
    compat1 = ⊑-compatible· (choose⊑· name w1l (T→ℂ· (NUM 0))) compatl

    wgt0 : ∀𝕎-get0-NUM w1s' name
    wgt0 = cn name w1l 0 compatl

    nnf : ¬ name ∈ names ⌜ f ⌝
    nnf = ¬newChoiceT-testMLup∈names-f w1' ⌜ F ⌝ ⌜ f ⌝

    nnF : ¬ name ∈ names ⌜ F ⌝
    nnF = ¬newChoiceT-testMLup∈names-F w1' ⌜ F ⌝ ⌜ f ⌝

    uF : updCtxt2 name ⌜ f ⌝ ⌜ F ⌝
    uF = updCtxt2-refl name ⌜ f ⌝ ⌜ F ⌝ nnF

    nnw1' : ¬ name ∈ names𝕎· w1'
    nnw1' = ¬newChoiceT-testMLup∈names𝕎 w1' ⌜ F ⌝ ⌜ f ⌝

    nnw1s' : ¬ name ∈ names𝕎· w1s'
    nnw1s' i = nnw1' (∈names𝕎-startNewChoiceT→ cc name w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝) (names𝕎-startNewChoices→ cc w1s ⌜ F ⌝ name (names𝕎-chooseT→ cc name name w1l (NUM 0) i)))

    idomw1s' : name ∈ dom𝕎· w1s'
    idomw1s' = dom𝕎-chooseT cc name name w1l (NUM 0) (⊆dom𝕎-startNewChoices cc w1s ⌜ F ⌝ (newChoiceT∈dom𝕎 cc w1' (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)))

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
    ish = proj₁ pish gt0 {--fst pish ?--}

{--
    aw : ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) ((k : ℕ) → #APPLY F (#force f) #⇓ #NUM k at w' → #APPLY F (#force g) #⇓ #NUM k at w'))
    aw w1 e1 = lift imp
      where
        -- TODO: this is what we have to prove
        -- We want to use eqfgq-aux on w0=w1s' & w1s'=w1s' & w1=w1s' too
        -- and then use →equalInType-NAT-⊑
        imp : (k : ℕ) → #APPLY F (#force f) #⇓ #NUM k at w1 → #APPLY F (#force g) #⇓ #NUM k at w1
        imp k' c = {!!}
--}

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

    -- TODO: can we get rid of these 2 assumptions?
    aw1 : (k' : ℕ) → #APPLY F (#force f) #⇓ #NUM k' at w1s' → #APPLY F (#force g) #⇓ #NUM k' at w1s'
    aw1 k' c = eqfgq-aux
                 cc cn kb gc {i} {w1s'} {w1s'} {w1s'} {w2} {F} {f} {g} {name} {k} {v} {j} {tn}
                 nnF nnf nnw1s' idomw1s' idomw1s' nFw1s' nFw1s' {!!} {!!}
                 (upto𝕎-refl name w1s') compat1 compat1 wgt0 g0
                 eqj isvv (⊑-refl· w1s') (⊑-refl· w1s') wgt0 (equalInType-mon ∈F w1s' e0'') (equalInType-mon ∈f w1s' e0'')
                 (∀𝕎-mon e0' eqb5) compa k' c

    eqnw1s' : equalInType i w1s' #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqnw1s' = →→equalInType-NAT
                kb
                (equalInType-mon (equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f))) w1s' e0'')
                (equalInType-mon (equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈g))) w1s' e0'')
                aw1

    eqf : equalInType i w #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqf = equalInType-NAT-mon-rev
            kb
            (equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f)))
            (equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
            e0'' eqnw1s'



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

\end{code}
