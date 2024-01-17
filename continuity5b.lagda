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
open import encode


module continuity5b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice)
                    (K : Compatible {L} W C)
                    (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC) using (shiftUp-shiftNameUp)
open import terms3(W)(C)(K)(G)(X)(N)(EC) using (updBody ; sucIf≤-sucIf≤ ; suc≡sucIf≤0 ; shiftNameUp-shiftNameUp ; suc→∈lowerNames ; upd ; ≡LAMBDA ; ≡LET ; ≡IFLT ; ≡CS ; ≡CHOOSE ; ≡APPLY ; ≡NAME)
open import terms4(W)(C)(K)(G)(X)(N)(EC) using (→¬∈names-shiftUp)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
--open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC) using (CSinj)
--open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

--open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(G)(X)(N)(EC) using (UNIVinj)
--open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
--open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC

--open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(G)(X)(N)(EC) using (force)
--open import continuity2(W)(M)(C)(K)(G)(X)(N)(EC) using (isHighestℕ)
--open import continuity3(W)(M)(C)(K)(G)(X)(N)(EC)
--open import continuity4(W)(M)(C)(K)(G)(X)(N)(EC)
--open import continuity5(W)(M)(C)(K)(G)(X)(N)(EC)

open import continuity1b(W)(M)(C)(K)(G)(X)(N)(EC) using (→≡sucIf≤ ; NAMEinj ; shiftNameUp-inj) --using (→≡sucIf≤ ; shiftNameUp-inj ; updBody≡shiftNameUp→ ; shiftNameUpDown ; ¬∈++2→¬∈1 ; ¬∈++2→¬∈2 ; ¬∈++4→¬∈1 ; ¬∈++4→¬∈2 ; ¬∈++4→¬∈3 ; ¬∈++4→¬∈4)
--open import continuity2b(W)(M)(C)(K)(G)(X)(N)(EC) using (∈names𝕎)
--open import continuity3b(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity4b(W)(M)(C)(K)(G)(X)(N)(EC)


abstract
  upd-shift→≡shift : (n : ℕ) (name : Name) (f a : Term)
                      → upd (sucIf≤ n name) (shiftNameUp n f) ≡ shiftNameUp n a
                      → a ≡ upd name f
  upd-shift→≡shift n name f (LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS n1) (NUM 0)) (VAR 0) (CHOOSE (NAME n2) (VAR 0)) AX) (APPLY a (VAR 1))))) e
    = ≡LAMBDA (≡LET refl (≡LET (≡IFLT (≡APPLY (≡CS (sym (sucIf≤-inj (CSinj (APPLYinj1 (IFLTinj1 ((LETinj1 (LETinj2 (LAMinj e)))))))))) refl)
                                      refl
                                      (≡CHOOSE (≡NAME (sym (sucIf≤-inj (NAMEinj (CHOOSEinj1 (IFLTinj3 ((LETinj1 (LETinj2 (LAMinj e)))))))))) refl)
                                      refl)
                               (≡APPLY (shiftNameUp-inj (trans (sym (APPLYinj1 (LETinj2 (LETinj2 (LAMinj e))))) (shiftUp-shiftNameUp 0 n f))) refl)))


abstract
  force-shift→≡shift : (n : ℕ) (g a : Term)
                      → force (shiftNameUp n g) ≡ shiftNameUp n a
                      → a ≡ force g
  force-shift→≡shift n g (LAMBDA (LET (VAR 0) (APPLY b (VAR 0)))) e
    rewrite shiftNameUp-inj (APPLYinj1 (LETinj2 (LAMinj e))) = refl


abstract
  updRel2-shiftNameUp≡→upd : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                            → upd (sucIf≤ n name) (shiftNameUp n f) ≡ shiftNameUp n a
                            → force (shiftNameUp n g) ≡ shiftNameUp n b
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→upd n {name} {f} {g} {r} cf cg {a} {b} equ eqv
    rewrite upd-shift→≡shift n name f a equ
          | force-shift→≡shift n g b eqv
    = updRel2-upd


abstract
  updRel2-shiftNameUp≡→VAR : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x : Var}
                          → VAR x ≡ shiftNameUp n a
                          → VAR x ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→VAR n {name} {f} {g} {r} cf cg {VAR x₁} {VAR x₂} {x} equ eqv
    rewrite VARinj equ | VARinj eqv = updRel2-VAR _


{-
abstract
  updRel2-shiftNameUp≡→NAT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → NAT ≡ shiftNameUp n a
                          → NAT ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NAT n {name} {f} {g} {r} cf cg {NAT} {NAT} equ eqv = updRel2-NAT
-}


abstract
  updRel2-shiftNameUp≡→QNAT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → QNAT ≡ shiftNameUp n a
                          → QNAT ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→QNAT n {name} {f} {g} {r} cf cg {QNAT} {QNAT} equ eqv = updRel2-QNAT


{-
abstract
  updRel2-shiftNameUp≡→TNAT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → TNAT ≡ shiftNameUp n a
                          → TNAT ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→TNAT n {name} {f} {g} {r} cf cg {TNAT} {TNAT} equ eqv = updRel2-TNAT
-}


abstract
  updRel2-shiftNameUp≡→AX : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → AX ≡ shiftNameUp n a
                          → AX ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→AX n {name} {f} {g} {r} cf cg {AX} {AX} equ eqv = updRel2-AX


abstract
  updRel2-shiftNameUp≡→FREE : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → FREE ≡ shiftNameUp n a
                          → FREE ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→FREE n {name} {f} {g} {r} cf cg {FREE} {FREE} equ eqv = updRel2-FREE


abstract
  updRel2-shiftNameUp≡→PURE : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → PURE ≡ shiftNameUp n a
                          → PURE ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→PURE n {name} {f} {g} {r} cf cg {PURE} {PURE} equ eqv = updRel2-PURE


abstract
  updRel2-shiftNameUp≡→NOSEQ : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → NOSEQ ≡ shiftNameUp n a
                          → NOSEQ ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NOSEQ n {name} {f} {g} {r} cf cg {NOSEQ} {NOSEQ} equ eqv = updRel2-NOSEQ


abstract
  updRel2-shiftNameUp≡→NOENC : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                          → NOENC ≡ shiftNameUp n a
                          → NOENC ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NOENC n {name} {f} {g} {r} cf cg {NOENC} {NOENC} equ eqv = updRel2-NOENC


abstract
  updRel2-shiftNameUp≡→LT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → LT x₁ y₁ ≡ shiftNameUp n a
                            → LT x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→LT n {name} {f} {g} {r} cf cg {LT u₁ v₁} {LT u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite LTinj1 equ | LTinj2 equ | LTinj1 eqv | LTinj2 eqv
    = updRel2-LT u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→QLT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → QLT x₁ y₁ ≡ shiftNameUp n a
                            → QLT x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→QLT n {name} {f} {g} {r} cf cg {QLT u₁ v₁} {QLT u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite QLTinj1 equ | QLTinj2 equ | QLTinj1 eqv | QLTinj2 eqv
    = updRel2-QLT u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→NUM : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x : ℕ}
                          → NUM x ≡ shiftNameUp n a
                          → NUM x ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NUM n {name} {f} {g} {r} cf cg {NUM x₁} {NUM x₂} {x} equ eqv
    rewrite NUMinj equ | NUMinj eqv = updRel2-NUM _


abstract
  updRel2-shiftNameUp≡→UNIV : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x : ℕ}
                          → UNIV x ≡ shiftNameUp n a
                          → UNIV x ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→UNIV n {name} {f} {g} {r} cf cg {UNIV x₁} {UNIV x₂} {x} equ eqv
    rewrite UNIVinj equ | UNIVinj eqv = updRel2-UNIV _


abstract
  updRel2-shiftNameUp≡→LOAD : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x : Term}
                          → LOAD x ≡ shiftNameUp n a
                          → LOAD x ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→LOAD n {name} {f} {g} {r} cf cg {LOAD x₁} {LOAD x₂} {x} equ eqv
    rewrite sym (LOADinj equ) | sym (LOADinj eqv) = updRel2-LOAD _


abstract
  updRel2-shiftNameUp≡→CS : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x₁ x₂ : Name}
                          → CS x₁ ≡ shiftNameUp n a
                          → CS x₂ ≡ shiftNameUp n b
                          → names∈ren x₁ x₂ (sucIf≤-ren n r)
                          → ¬ x₁ ≡ sucIf≤ n name
                          → ¬ x₂ ≡ sucIf≤ n name
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→CS n {name} {f} {g} {r} cf cg {CS y₁} {CS y₂} {x₁} {x₂} equ eqv ni1 ni2 ni3
    rewrite CSinj equ | CSinj eqv
    = updRel2-CS y₁ y₂ (λ z → ni2 (→≡sucIf≤ z)) (λ z → ni3 (→≡sucIf≤ z)) (names∈ren-sucIf≤-ren→ n y₁ y₂ r ni1)


abstract
  updRel2-shiftNameUp≡→NAME : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x₁ x₂ : Name}
                          → NAME x₁ ≡ shiftNameUp n a
                          → NAME x₂ ≡ shiftNameUp n b
                          → names∈ren x₁ x₂ (sucIf≤-ren n r)
                          → ¬ x₁ ≡ sucIf≤ n name
                          → ¬ x₂ ≡ sucIf≤ n name
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NAME n {name} {f} {g} {r} cf cg {NAME y₁} {NAME y₂} {x₁} {x₂} equ eqv ni1 ni2 ni3
    rewrite NAMEinj equ | NAMEinj eqv
    = updRel2-NAME y₁ y₂ (λ z → ni2 (→≡sucIf≤ z)) (λ z → ni3 (→≡sucIf≤ z)) (names∈ren-sucIf≤-ren→ n y₁ y₂ r ni1)


abstract
  updRel2-shiftNameUp≡→MSEQ : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {x : 𝕊}
                          → MSEQ x ≡ shiftNameUp n a
                          → MSEQ x ≡ shiftNameUp n b
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→MSEQ n {name} {f} {g} {r} cf cg {MSEQ x₁} {MSEQ x₂} {x} equ eqv
    rewrite MSEQinj equ | MSEQinj eqv = updRel2-MSEQ _


abstract
  updRel2-shiftNameUp≡→PI : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → PI x₁ y₁ ≡ shiftNameUp n a
                            → PI x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→PI n {name} {f} {g} {r} cf cg {PI u₁ v₁} {PI u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite PIinj1 equ | PIinj2 equ | PIinj1 eqv | PIinj2 eqv
    = updRel2-PI u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→APPLY : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → APPLY x₁ y₁ ≡ shiftNameUp n a
                            → APPLY x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→APPLY n {name} {f} {g} {r} cf cg {APPLY u₁ v₁} {APPLY u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite APPLYinj1 equ | APPLYinj2 equ | APPLYinj1 eqv | APPLYinj2 eqv
    = updRel2-APPLY u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→LET : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → LET x₁ y₁ ≡ shiftNameUp n a
                            → LET x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→LET n {name} {f} {g} {r} cf cg {LET u₁ v₁} {LET u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite LETinj1 equ | LETinj2 equ | LETinj1 eqv | LETinj2 eqv
    = updRel2-LET u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→SUM : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SUM x₁ y₁ ≡ shiftNameUp n a
                            → SUM x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SUM n {name} {f} {g} {r} cf cg {SUM u₁ v₁} {SUM u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite SUMinj1 equ | SUMinj2 equ | SUMinj1 eqv | SUMinj2 eqv
    = updRel2-SUM u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→PAIR : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → PAIR x₁ y₁ ≡ shiftNameUp n a
                            → PAIR x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→PAIR n {name} {f} {g} {r} cf cg {PAIR u₁ v₁} {PAIR u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite PAIRinj1 equ | PAIRinj2 equ | PAIRinj1 eqv | PAIRinj2 eqv
    = updRel2-PAIR u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→SPREAD : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SPREAD x₁ y₁ ≡ shiftNameUp n a
                            → SPREAD x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SPREAD n {name} {f} {g} {r} cf cg {SPREAD u₁ v₁} {SPREAD u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite SPREADinj1 equ | SPREADinj2 equ | SPREADinj1 eqv | SPREADinj2 eqv
    = updRel2-SPREAD u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→WT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → WT x₁ y₁ z₁ ≡ shiftNameUp n a
                            → WT x₂ y₂ z₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→WT n {name} {f} {g} {r} cf cg {WT u₁ v₁ w₁} {WT u₂ v₂ w₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} ind1 ind2 ind3 equ eqv ur1 ur2 ur3
    rewrite Winj1 equ | Winj2 equ | Winj3 equ | Winj1 eqv | Winj2 eqv | Winj3 eqv
    = updRel2-WT u₁ u₂ v₁ v₂ w₁ w₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl) (ind3 w₁ w₂ refl refl)


abstract
  updRel2-shiftNameUp≡→MT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → MT x₁ y₁ z₁ ≡ shiftNameUp n a
                            → MT x₂ y₂ z₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→MT n {name} {f} {g} {r} cf cg {MT u₁ v₁ w₁} {MT u₂ v₂ w₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} ind1 ind2 ind3 equ eqv ur1 ur2 ur3
    rewrite Minj1 equ | Minj2 equ | Minj3 equ | Minj1 eqv | Minj2 eqv | Minj3 eqv
    = updRel2-MT u₁ u₂ v₁ v₂ w₁ w₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl) (ind3 w₁ w₂ refl refl)


abstract
  updRel2-shiftNameUp≡→SUP : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SUP x₁ y₁ ≡ shiftNameUp n a
                            → SUP x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SUP n {name} {f} {g} {r} cf cg {SUP u₁ v₁} {SUP u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite SUPinj1 equ | SUPinj2 equ | SUPinj1 eqv | SUPinj2 eqv
    = updRel2-SUP u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→WREC : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → WREC x₁ y₁ ≡ shiftNameUp n a
                            → WREC x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→WREC n {name} {f} {g} {r} cf cg {WREC u₁ v₁} {WREC u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite WRECinj1 equ | WRECinj2 equ | WRECinj1 eqv | WRECinj2 eqv
    = updRel2-WREC u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→SET : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SET x₁ y₁ ≡ shiftNameUp n a
                            → SET x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SET n {name} {f} {g} {r} cf cg {SET u₁ v₁} {SET u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite SETinj1 equ | SETinj2 equ | SETinj1 eqv | SETinj2 eqv
    = updRel2-SET u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→ISECT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ISECT x₁ y₁ ≡ shiftNameUp n a
                            → ISECT x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→ISECT n {name} {f} {g} {r} cf cg {ISECT u₁ v₁} {ISECT u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite ISECTinj1 equ | ISECTinj2 equ | ISECTinj1 eqv | ISECTinj2 eqv
    = updRel2-ISECT u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→UNION : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → UNION x₁ y₁ ≡ shiftNameUp n a
                            → UNION x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→UNION n {name} {f} {g} {r} cf cg {UNION u₁ v₁} {UNION u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite UNIONinj1 equ | UNIONinj2 equ | UNIONinj1 eqv | UNIONinj2 eqv
    = updRel2-UNION u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→TUNION : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → TUNION x₁ y₁ ≡ shiftNameUp n a
                            → TUNION x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→TUNION n {name} {f} {g} {r} cf cg {TUNION u₁ v₁} {TUNION u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite TUNIONinj1 equ | TUNIONinj2 equ | TUNIONinj1 eqv | TUNIONinj2 eqv
    = updRel2-TUNION u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)

{-
abstract
  updRel2-shiftNameUp≡→QTUNION : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → QTUNION x₁ y₁ ≡ shiftNameUp n a
                            → QTUNION x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→QTUNION n {name} {f} {g} {r} cf cg {QTUNION u₁ v₁} {QTUNION u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite QTUNIONinj1 equ | QTUNIONinj2 equ | QTUNIONinj1 eqv | QTUNIONinj2 eqv
    = updRel2-QTUNION u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)
-}

abstract
  updRel2-shiftNameUp≡→INL : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → INL x₁ ≡ shiftNameUp n a
                            → INL x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→INL n {name} {f} {g} {r} cf cg {INL u₁} {INL u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite INLinj equ | INLinj eqv
    = updRel2-INL u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→INR : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → INR x₁ ≡ shiftNameUp n a
                            → INR x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→INR n {name} {f} {g} {r} cf cg {INR u₁} {INR u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite INRinj equ | INRinj eqv
    = updRel2-INR u₁ u₂ (ind1 u₁ u₂ refl refl)


{--
abstract
  updRel2-shiftNameUp≡→TSQUASH : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → TSQUASH x₁ ≡ shiftNameUp n a
                            → TSQUASH x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→TSQUASH n {name} {f} {g} {r} cf cg {TSQUASH u₁} {TSQUASH u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite TSQUASHinj equ | TSQUASHinj eqv
    = updRel2-TSQUASH u₁ u₂ (ind1 u₁ u₂ refl refl)
--}


{-
abstract
  updRel2-shiftNameUp≡→TTRUNC : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → TTRUNC x₁ ≡ shiftNameUp n a
                            → TTRUNC x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→TTRUNC n {name} {f} {g} {r} cf cg {TTRUNC u₁} {TTRUNC u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite TTRUNCinj equ | TTRUNCinj eqv
    = updRel2-TTRUNC u₁ u₂ (ind1 u₁ u₂ refl refl)
-}


abstract
  updRel2-shiftNameUp≡→NOWRITE : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                            → NOWRITE ≡ shiftNameUp n a
                            → NOWRITE ≡ shiftNameUp n b
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NOWRITE n {name} {f} {g} {r} cf cg {NOWRITE} {NOWRITE} equ eqv = updRel2-NOWRITE


abstract
  updRel2-shiftNameUp≡→NOREAD : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                            → NOREAD ≡ shiftNameUp n a
                            → NOREAD ≡ shiftNameUp n b
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NOREAD n {name} {f} {g} {r} cf cg {NOREAD} {NOREAD} equ eqv = updRel2-NOREAD


abstract
  updRel2-shiftNameUp≡→SUBSING : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SUBSING x₁ ≡ shiftNameUp n a
                            → SUBSING x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SUBSING n {name} {f} {g} {r} cf cg {SUBSING u₁} {SUBSING u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite SUBSINGinj equ | SUBSINGinj eqv
    = updRel2-SUBSING u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→PARTIAL : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → PARTIAL x₁ ≡ shiftNameUp n a
                            → PARTIAL x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→PARTIAL n {name} {f} {g} {r} cf cg {PARTIAL u₁} {PARTIAL u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite PARTIALinj equ | PARTIALinj eqv
    = updRel2-PARTIAL u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→LIFT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → LIFT x₁ ≡ shiftNameUp n a
                            → LIFT x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→LIFT n {name} {f} {g} {r} cf cg {LIFT u₁} {LIFT u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite LIFTinj equ | LIFTinj eqv
    = updRel2-LIFT u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→LOWER : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → LOWER x₁ ≡ shiftNameUp n a
                            → LOWER x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→LOWER n {name} {f} {g} {r} cf cg {LOWER u₁} {LOWER u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite LOWERinj equ | LOWERinj eqv
    = updRel2-LOWER u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→SHRINK : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SHRINK x₁ ≡ shiftNameUp n a
                            → SHRINK x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SHRINK n {name} {f} {g} {r} cf cg {SHRINK u₁} {SHRINK u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite SHRINKinj equ | SHRINKinj eqv
    = updRel2-SHRINK u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→SUC : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → SUC x₁ ≡ shiftNameUp n a
                            → SUC x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→SUC n {name} {f} {g} {r} cf cg {SUC u₁} {SUC u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite SUCinj equ | SUCinj eqv
    = updRel2-SUC u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→NATREC : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → NATREC x₁ y₁ z₁ ≡ shiftNameUp n a
                            → NATREC x₂ y₂ z₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→NATREC n {name} {f} {g} {r} cf cg {NATREC u₁ v₁ w₁} {NATREC u₂ v₂ w₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} ind1 ind2 ind3 equ eqv ur1
    rewrite NATRECinj1 equ | NATRECinj2 equ | NATRECinj3 equ
          | NATRECinj1 eqv | NATRECinj2 eqv | NATRECinj3 eqv
    = updRel2-NATREC u₁ u₂ v₁ v₂ w₁ w₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl) (ind3 w₁ w₂ refl refl)


abstract
  updRel2-shiftNameUp≡→LAMBDA : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → LAMBDA x₁ ≡ shiftNameUp n a
                            → LAMBDA x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→LAMBDA n {name} {f} {g} {r} cf cg {LAMBDA u₁} {LAMBDA u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite LAMinj equ | LAMinj eqv
    = updRel2-LAMBDA u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→FIX : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → FIX x₁ ≡ shiftNameUp n a
                            → FIX x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→FIX n {name} {f} {g} {r} cf cg {FIX u₁} {FIX u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite FIXinj equ | FIXinj eqv
    = updRel2-FIX u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→TERM : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → TERM x₁ ≡ shiftNameUp n a
                            → TERM x₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→TERM n {name} {f} {g} {r} cf cg {TERM u₁} {TERM u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite TERMinj equ | TERMinj eqv
    = updRel2-TERM u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→ENC : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x : Term}
                            → ((u₁ u₂ : Term) → x ≡ shiftNameUp n u₁ → x ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ENC x ≡ shiftNameUp n a
                            → ENC x ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x x
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→ENC n {name} {f} {g} {r} cf cg {ENC u₁} {ENC u₂} {x} ind1 equ eqv ur1
    rewrite ENCinj equ | shiftNameUp-inj {n} {u₁} {u₂} (ENCinj eqv)
    = updRel2-ENC u₂ (ind1 u₂ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→FRESH : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp (suc n) u₁ → x₂ ≡ shiftNameUp (suc n) u₂ → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) (sren r) u₁ u₂)
                            → FRESH x₁ ≡ shiftNameUp n a
                            → FRESH x₂ ≡ shiftNameUp n b
                            → updRel2 (suc (sucIf≤ n name)) (shiftNameUp 0 (shiftNameUp n f)) (shiftNameUp 0 (shiftNameUp n g)) (sren (sucIf≤-ren n r)) x₁ x₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→FRESH n {name} {f} {g} {r} cf cg {FRESH u₁} {FRESH u₂} {x₁} {x₂} ind1 equ eqv ur1
    rewrite FRESHinj equ | FRESHinj eqv
    = updRel2-FRESH u₁ u₂ (ind1 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→IFLT : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → w₁ ≡ shiftNameUp n u₁ → w₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → IFLT x₁ y₁ z₁ w₁ ≡ shiftNameUp n a
                            → IFLT x₂ y₂ z₂ w₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) w₁ w₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→IFLT n {name} {f} {g} {r} cf cg {IFLT s₁ t₁ u₁ v₁} {IFLT s₂ t₂ u₂ v₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} {w₁} {w₂} ind1 ind2 ind3 ind4 equ eqv ur1 ur2 ur3 ur4
    rewrite IFLTinj1 equ | IFLTinj2 equ | IFLTinj3 equ | IFLTinj4 equ
          | IFLTinj1 eqv | IFLTinj2 eqv | IFLTinj3 eqv | IFLTinj4 eqv
    = updRel2-IFLT s₁ s₂ t₁ t₂ u₁ u₂ v₁ v₂ (ind1 s₁ s₂ refl refl) (ind2 t₁ t₂ refl refl) (ind3 u₁ u₂ refl refl) (ind4 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→IFEQ : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → w₁ ≡ shiftNameUp n u₁ → w₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → IFEQ x₁ y₁ z₁ w₁ ≡ shiftNameUp n a
                            → IFEQ x₂ y₂ z₂ w₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) w₁ w₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→IFEQ n {name} {f} {g} {r} cf cg {IFEQ s₁ t₁ u₁ v₁} {IFEQ s₂ t₂ u₂ v₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} {w₁} {w₂} ind1 ind2 ind3 ind4 equ eqv ur1 ur2 ur3 ur4
    rewrite IFEQinj1 equ | IFEQinj2 equ | IFEQinj3 equ | IFEQinj4 equ
          | IFEQinj1 eqv | IFEQinj2 eqv | IFEQinj3 eqv | IFEQinj4 eqv
    = updRel2-IFEQ s₁ s₂ t₁ t₂ u₁ u₂ v₁ v₂ (ind1 s₁ s₂ refl refl) (ind2 t₁ t₂ refl refl) (ind3 u₁ u₂ refl refl) (ind4 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→MAPP : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term} {s : 𝕊} {y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → MAPP s y₁ ≡ shiftNameUp n a
                            → MAPP s y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→MAPP n {name} {f} {g} {r} cf cg {MAPP u₁ v₁} {MAPP u₂ v₂} {s} {y₁} {y₂} ind1 equ eqv ur1
    rewrite MAPPinj1 equ | MAPPinj2 equ | MAPPinj1 eqv | MAPPinj2 eqv
    = updRel2-MAPP u₂ v₁ v₂ (ind1 v₁ v₂ refl refl)


{-
abstract
  updRel2-shiftNameUp≡→EQB : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → w₁ ≡ shiftNameUp n u₁ → w₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → EQB x₁ y₁ z₁ w₁ ≡ shiftNameUp n a
                            → EQB x₂ y₂ z₂ w₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) w₁ w₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→EQB n {name} {f} {g} {r} cf cg {EQB s₁ t₁ u₁ v₁} {EQB s₂ t₂ u₂ v₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} {w₁} {w₂} ind1 ind2 ind3 ind4 equ eqv ur1 ur2 ur3 ur4
    rewrite EQBinj1 equ | EQBinj2 equ | EQBinj3 equ | EQBinj4 equ
          | EQBinj1 eqv | EQBinj2 eqv | EQBinj3 eqv | EQBinj4 eqv
    = updRel2-EQB s₁ s₂ t₁ t₂ u₁ u₂ v₁ v₂ (ind1 s₁ s₂ refl refl) (ind2 t₁ t₂ refl refl) (ind3 u₁ u₂ refl refl) (ind4 v₁ v₂ refl refl)
-}


abstract
  updRel2-shiftNameUp≡→DECIDE : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → DECIDE x₁ y₁ z₁ ≡ shiftNameUp n a
                            → DECIDE x₂ y₂ z₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→DECIDE n {name} {f} {g} {r} cf cg {DECIDE s₁ t₁ u₁} {DECIDE s₂ t₂ u₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} ind1 ind2 ind3 equ eqv ur1 ur2 ur3
    rewrite DECIDEinj1 equ | DECIDEinj2 equ | DECIDEinj3 equ
          | DECIDEinj1 eqv | DECIDEinj2 eqv | DECIDEinj3 eqv
    = updRel2-DECIDE s₁ s₂ t₁ t₂ u₁ u₂ (ind1 s₁ s₂ refl refl) (ind2 t₁ t₂ refl refl) (ind3 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→EQ : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ z₁ z₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → z₁ ≡ shiftNameUp n u₁ → z₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → EQ x₁ y₁ z₁ ≡ shiftNameUp n a
                            → EQ x₂ y₂ z₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) z₁ z₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→EQ n {name} {f} {g} {r} cf cg {EQ s₁ t₁ u₁} {EQ s₂ t₂ u₂} {x₁} {x₂} {y₁} {y₂} {z₁} {z₂} ind1 ind2 ind3 equ eqv ur1 ur2 ur3
    rewrite EQinj1 equ | EQinj2 equ | EQinj3 equ
          | EQinj1 eqv | EQinj2 eqv | EQinj3 eqv
    = updRel2-EQ s₁ s₂ t₁ t₂ u₁ u₂ (ind1 s₁ s₂ refl refl) (ind2 t₁ t₂ refl refl) (ind3 u₁ u₂ refl refl)


abstract
  updRel2-shiftNameUp≡→CHOOSE : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → CHOOSE x₁ y₁ ≡ shiftNameUp n a
                            → CHOOSE x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→CHOOSE n {name} {f} {g} {r} cf cg {CHOOSE u₁ v₁} {CHOOSE u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite CHOOSEinj1 equ | CHOOSEinj2 equ | CHOOSEinj1 eqv | CHOOSEinj2 eqv
    = updRel2-CHOOSE u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→FFDEFS : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b x₁ x₂ y₁ y₂ : Term}
                            → ((u₁ u₂ : Term) → x₁ ≡ shiftNameUp n u₁ → x₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → ((u₁ u₂ : Term) → y₁ ≡ shiftNameUp n u₁ → y₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂)
                            → FFDEFS x₁ y₁ ≡ shiftNameUp n a
                            → FFDEFS x₂ y₂ ≡ shiftNameUp n b
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) x₁ x₂
                            → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) y₁ y₂
                            → updRel2 name f g r a b
  updRel2-shiftNameUp≡→FFDEFS n {name} {f} {g} {r} cf cg {FFDEFS u₁ v₁} {FFDEFS u₂ v₂} {x₁} {x₂} {y₁} {y₂} ind1 ind2 equ eqv ur1 ur2
    rewrite FFDEFSinj1 equ | FFDEFSinj2 equ | FFDEFSinj1 eqv | FFDEFSinj2 eqv
    = updRel2-FFDEFS u₁ u₂ v₁ v₂ (ind1 u₁ u₂ refl refl) (ind2 v₁ v₂ refl refl)


abstract
  updRel2-shiftNameUp≡→ : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b u v : Term}
                          → u ≡ shiftNameUp n a
                          → v ≡ shiftNameUp n b
                          → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) u v
                          → updRel2 name f g r a b
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(VAR x)} {.(VAR x)} equ eqv (updRel2-VAR x) = updRel2-shiftNameUp≡→VAR n cf cg equ eqv
--  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.NAT} {.NAT} equ eqv updRel2-NAT = updRel2-shiftNameUp≡→NAT n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.QNAT} {.QNAT} equ eqv updRel2-QNAT = updRel2-shiftNameUp≡→QNAT n cf cg equ eqv
--  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.TNAT} {.TNAT} equ eqv updRel2-TNAT = updRel2-shiftNameUp≡→TNAT n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(LT a₁ b₁)} {.(LT a₂ b₂)} equ eqv (updRel2-LT a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→LT n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} equ eqv (updRel2-QLT a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→QLT n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(NUM x)} {.(NUM x)} equ eqv (updRel2-NUM x) = updRel2-shiftNameUp≡→NUM n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} equ eqv (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃)
    = updRel2-shiftNameUp≡→IFLT n cf cg ind1 ind2 ind3 ind4 equ eqv ur ur₁ ur₂ ur₃
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂

      ind4 : (u₁ u₂ : Term) → d₁ ≡ shiftNameUp n u₁ → d₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind4 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {d₁} {d₂} e₁ e₂ ur₃
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} equ eqv (updRel2-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃)
    = updRel2-shiftNameUp≡→IFEQ n cf cg ind1 ind2 ind3 ind4 equ eqv ur ur₁ ur₂ ur₃
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂

      ind4 : (u₁ u₂ : Term) → d₁ ≡ shiftNameUp n u₁ → d₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind4 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {d₁} {d₂} e₁ e₂ ur₃
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SUC a₁)} {.(SUC a₂)} equ eqv (updRel2-SUC a₁ a₂ ur)
    = updRel2-shiftNameUp≡→SUC n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(NATREC a₁ b₁ c₁)} {.(NATREC a₂ b₂ c₂)} equ eqv (updRel2-NATREC a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂)
    = updRel2-shiftNameUp≡→NATREC n cf cg ind1 ind2 ind3 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(PI a₁ b₁)} {.(PI a₂ b₂)} equ eqv (updRel2-PI a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→PI n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(LAMBDA a₁)} {.(LAMBDA a₂)} equ eqv (updRel2-LAMBDA a₁ a₂ ur)
    = updRel2-shiftNameUp≡→LAMBDA n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} equ eqv (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→APPLY n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(MSEQ s)} {.(MSEQ s)} equ eqv (updRel2-MSEQ s) = updRel2-shiftNameUp≡→MSEQ n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(MAPP s a₁)} {.(MAPP s a₂)} equ eqv (updRel2-MAPP s a₁ a₂ ur)
    = updRel2-shiftNameUp≡→MAPP n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(FIX a₁)} {.(FIX a₂)} equ eqv (updRel2-FIX a₁ a₂ ur)
    = updRel2-shiftNameUp≡→FIX n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(LET a₁ b₁)} {.(LET a₂ b₂)} equ eqv (updRel2-LET a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→LET n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} equ eqv (updRel2-SUM a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→SUM n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} equ eqv (updRel2-PAIR a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→PAIR n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} equ eqv (updRel2-SPREAD a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→SPREAD n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} equ eqv (updRel2-WT a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂)
    = updRel2-shiftNameUp≡→WT n cf cg ind1 ind2 ind3 equ eqv ur ur₁ ur₂
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} equ eqv (updRel2-SUP a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→SUP n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} equ eqv (updRel2-WREC a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→WREC n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} equ eqv (updRel2-MT a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂)
    = updRel2-shiftNameUp≡→MT n cf cg ind1 ind2 ind3 equ eqv ur ur₁ ur₂
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SET a₁ b₁)} {.(SET a₂ b₂)} equ eqv (updRel2-SET a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→SET n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} equ eqv (updRel2-ISECT a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→ISECT n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} equ eqv (updRel2-TUNION a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→TUNION n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} equ eqv (updRel2-UNION a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→UNION n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
{-  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} equ eqv (updRel2-QTUNION a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→QTUNION n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁-}
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(INL a₁)} {.(INL a₂)} equ eqv (updRel2-INL a₁ a₂ ur)
    = updRel2-shiftNameUp≡→INL n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(INR a₁)} {.(INR a₂)} equ eqv (updRel2-INR a₁ a₂ ur)
    = updRel2-shiftNameUp≡→INR n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} equ eqv (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂)
    = updRel2-shiftNameUp≡→DECIDE n cf cg ind1 ind2 ind3 equ eqv ur ur₁ ur₂
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} equ eqv (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂)
    = updRel2-shiftNameUp≡→EQ n cf cg ind1 ind2 ind3 equ eqv ur ur₁ ur₂
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂
{-  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} equ eqv (updRel2-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃)
    = updRel2-shiftNameUp≡→EQB n cf cg ind1 ind2 ind3 ind4 equ eqv ur ur₁ ur₂ ur₃
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁

      ind3 : (u₁ u₂ : Term) → c₁ ≡ shiftNameUp n u₁ → c₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind3 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {c₁} {c₂} e₁ e₂ ur₂

      ind4 : (u₁ u₂ : Term) → d₁ ≡ shiftNameUp n u₁ → d₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind4 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {d₁} {d₂} e₁ e₂ ur₃-}
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.AX} {.AX} equ eqv updRel2-AX = updRel2-shiftNameUp≡→AX n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.FREE} {.FREE} equ eqv updRel2-FREE = updRel2-shiftNameUp≡→FREE n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(CS name1)} {.(CS name2)} equ eqv (updRel2-CS name1 name2 x x₁ x₂) = updRel2-shiftNameUp≡→CS n cf cg equ eqv x₂ x x₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(NAME name1)} {.(NAME name2)} equ eqv (updRel2-NAME name1 name2 x x₁ x₂) = updRel2-shiftNameUp≡→NAME n cf cg equ eqv x₂ x x₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(FRESH a₁)} {.(FRESH a₂)} equ eqv (updRel2-FRESH a₁ a₂ ur)
    = updRel2-shiftNameUp≡→FRESH n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp (suc n) u₁ → a₂ ≡ shiftNameUp (suc n) u₂ → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) (sren r) u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ (suc n) {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur1
        where
          seq1 : suc (sucIf≤ n name) ≡ sucIf≤ (suc n) (sucIf≤ 0 name)
          seq1 rewrite sym (sucIf≤-sucIf≤ {name} {0} {n} _≤_.z≤n) | sym (suc≡sucIf≤0 (sucIf≤ n name)) = refl

          seq2 : sren (sucIf≤-ren n r) ≡ sucIf≤-ren (suc n) (sren r)
          seq2 = sym (sucIf≤-ren-suc-sren n r)

          ur1 : updRel2 (sucIf≤ (suc n) (suc name))
                        (shiftNameUp (suc n) (shiftNameUp 0 f))
                        (shiftNameUp (suc n) (shiftNameUp 0 g))
                        (sucIf≤-ren (suc n) (sren r))
                        a₁
                        a₂
          ur1 rewrite suc≡sucIf≤0 name | sym seq1 | sym seq2 | sym (shiftNameUp-shiftNameUp {0} {n} {f} _≤_.z≤n) | sym (shiftNameUp-shiftNameUp {0} {n} {g} _≤_.z≤n) = ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(LOAD a₁)} {.(LOAD a₁)} equ eqv (updRel2-LOAD a₁) = updRel2-shiftNameUp≡→LOAD n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} equ eqv (updRel2-CHOOSE a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→CHOOSE n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
{--  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(TSQUASH a₁)} {.(TSQUASH a₂)} equ eqv (updRel2-TSQUASH a₁ a₂ ur)
    = updRel2-shiftNameUp≡→TSQUASH n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur--}
{-  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(TTRUNC a₁)} {.(TTRUNC a₂)} equ eqv (updRel2-TTRUNC a₁ a₂ ur)
    = updRel2-shiftNameUp≡→TTRUNC n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur-}
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.NOWRITE} {.NOWRITE} equ eqv updRel2-NOWRITE = updRel2-shiftNameUp≡→NOWRITE n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.NOREAD}  {.NOREAD}  equ eqv updRel2-NOREAD  = updRel2-shiftNameUp≡→NOREAD  n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SUBSING a₁)} {.(SUBSING a₂)} equ eqv (updRel2-SUBSING a₁ a₂ ur)
    = updRel2-shiftNameUp≡→SUBSING n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.PURE} {.PURE} equ eqv updRel2-PURE = updRel2-shiftNameUp≡→PURE n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.NOSEQ} {.NOSEQ} equ eqv updRel2-NOSEQ = updRel2-shiftNameUp≡→NOSEQ n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.NOENC} {.NOENC} equ eqv updRel2-NOENC = updRel2-shiftNameUp≡→NOENC n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(TERM a₁)} {.(TERM a₂)} equ eqv (updRel2-TERM a₁ a₂ ur)
    = updRel2-shiftNameUp≡→TERM n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(ENC a₁)} {.(ENC a₁)} equ eqv (updRel2-ENC a₁ ur)
    = updRel2-shiftNameUp≡→ENC n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₁ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₁} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(PARTIAL a₁)} {.(PARTIAL a₂)} equ eqv (updRel2-PARTIAL a₁ a₂ ur)
    = updRel2-shiftNameUp≡→PARTIAL n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} equ eqv (updRel2-FFDEFS a₁ a₂ b₁ b₂ ur ur₁)
    = updRel2-shiftNameUp≡→FFDEFS n cf cg ind1 ind2 equ eqv ur ur₁
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur

      ind2 : (u₁ u₂ : Term) → b₁ ≡ shiftNameUp n u₁ → b₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind2 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {b₁} {b₂} e₁ e₂ ur₁
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(UNIV x)} {.(UNIV x)} equ eqv (updRel2-UNIV x) = updRel2-shiftNameUp≡→UNIV n cf cg equ eqv
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(LIFT a₁)} {.(LIFT a₂)} equ eqv (updRel2-LIFT a₁ a₂ ur)
    = updRel2-shiftNameUp≡→LIFT n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(LOWER a₁)} {.(LOWER a₂)} equ eqv (updRel2-LOWER a₁ a₂ ur)
    = updRel2-shiftNameUp≡→LOWER n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(SHRINK a₁)} {.(SHRINK a₂)} equ eqv (updRel2-SHRINK a₁ a₂ ur)
    = updRel2-shiftNameUp≡→SHRINK n cf cg ind1 equ eqv ur
    where
      ind1 : (u₁ u₂ : Term) → a₁ ≡ shiftNameUp n u₁ → a₂ ≡ shiftNameUp n u₂ → updRel2 name f g r u₁ u₂
      ind1 u₁ u₂ e₁ e₂ = updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {u₁} {u₂} {a₁} {a₂} e₁ e₂ ur
  updRel2-shiftNameUp≡→ n {name} {f} {g} {r} cf cg {a} {b} {.(upd (sucIf≤ n name) (shiftNameUp n f))} {.(force (shiftNameUp n g))} equ eqv updRel2-upd
    = updRel2-shiftNameUp≡→upd n cf cg equ eqv

\end{code}
