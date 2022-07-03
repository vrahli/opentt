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
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity8b(W)(M)(C)(K)(P)(G)(X)(N)(E)



steps-updRel2 : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term} {k : ℕ}
               → ¬ name ∈ names f
               → ¬ name ∈ names g
               → # f
               → # g
               → presUpdRel2 n name f g k
steps-updRel2 cc gc {n} {name} {f} {g} {k} nnf nng cf cg =
  <ℕind _ (steps-updRel2-aux cc gc {n} {name} {f} {g} nnf nng cf cg) k



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
                   → ¬ name ∈ names f
                   → ¬ name ∈ names g
                   → # f
                   → # g
                   → names F ⊆ dom𝕎· w1
                   → names F ⊆ dom𝕎· w
                   → name ∈ dom𝕎· w1
                   → name ∈ dom𝕎· w
                   → names f ⊆ dom𝕎· w1
                   → names g ⊆ dom𝕎· w
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
steps-updRel2-app cc gc {n} {name} {F} {f} {g} {v} {w0} {w1} {w2} {w} {r} {k} nnf nng cf cg nFiw1 nFiw idom1 idom2 nfiw ngiw upw compat1 compat2 gt0 ww1 ww eqn comp ish inw isv =
  steps-updRel2
    cc gc {n} {name} {f} {g} {k} nnf nng cf cg
    {APPLY F (upd name f)} {APPLY F (force g)} {v} {w0} {w1} {w2} {w} {r}
    (updRel2-APPLY F F (upd name f) (force g) {!!} updRel2-upd)
    (→names-APPLY-upd⊆ {F} {f} {dom𝕎· w1} {name} nFiw1 idom1 nfiw)
    (→names-APPLY-force⊆ {F} {g} {dom𝕎· w} nFiw ngiw)
    idom2 nfiw ngiw upw compat1 compat2 gt0 ww1 ww eqn comp ish inw isv


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
        nnw1s' i = nnw1' (∈names𝕎-startNewChoiceT→ cc name w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝) (names𝕎-chooseT→ cc name name w1s (NUM 0) i))

        idomw1s' : name ∈ dom𝕎· w1s'
        idomw1s' = dom𝕎-chooseT cc name name w1s (NUM 0) (ContConds.ccNchoice cc w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝))

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
