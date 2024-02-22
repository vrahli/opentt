\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --lossy-unification #-}

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
open import compatible
open import getChoice
open import progress
open import choiceExt
open import newChoice
open import mod
open import encode


module props6 {L : Level}
              (W : PossibleWorlds {L})
              (M : Mod W)
              (C : Choice)
              (K : Compatible {L} W C)
              (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (TUNION-eq ; TUNION-eq-base ; TUNION-eq-trans ; TUNION-eq→ ; →TUNION-eq ; eqTypes-mon)
open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)
open import ind3(W)(M)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (steps→¬Names)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (SUM! ; #SUM! ; UNION! ; #UNION!)
--open import termsPres(W)(C)(K)(G)(X)(N)(EC)
--  using (#¬Enc→⇛! ; #¬Seq→⇛!)

open import type_sys_props_sum(W)(M)(C)(K)(G)(X)(N)(EC)
open import type_sys_props_isect(W)(M)(C)(K)(G)(X)(N)(EC)

open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
  using (□·EqTypes→uniUpTo ; uniUpTo→□·EqTypes ; ≡→#isValue ; equalInType→eqInType)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqInType-extr1 ; eqInType-sym ; eqInType-extl1 ; equalInType-sym ; equalInType-local ; eqTypes-local ;
         equalInType-mon ; ≡CTerm→eqTypes ; eqTypesNOREADMOD← ; eqTypesNOWRITEMOD← ; eqTypesSUM← ; equalInType-SUM→;
         equalInTypeNOREADMOD→ ; equalInTypeNOWRITEMOD→ ; NOWRITEMODeq ; NOREADMODeq ; equalInType-EQ ;
         →equalInTypeNOWRITEMOD ; →equalInTypeNOREADMOD ; #⇛val→#⇓→#⇛ ; equalInType-SUM ; eqTypesUNION← ;
         equalInType-UNION→)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalTypes-#⇛-left-rev ; TUNIONeq-#⇛-rev ; #⇛!-pres-hasValue ; #⇛!-pres-hasValue-rev ; →equalInType-UNION)

--open import uniMon(W)(M)(C)(K)(G)(X)(N)(EC)
--  using (equalTypes-uni-mon)


¬Names→names[] : {a : Term}
               → ¬names a ≡ true
               → names a ≡ []
¬Names→names[] {VAR x} nn = refl
¬Names→names[] {QNAT} nn = refl
¬Names→names[] {LT a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {QLT a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {NUM x} nn = refl
¬Names→names[] {IFLT a a₁ a₂ a₃} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn)))
      (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn)))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))))
¬Names→names[] {IFEQ a a₁ a₂ a₃} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn)))
      (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn)))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))))
¬Names→names[] {SUC a} nn = ¬Names→names[] {a} nn
¬Names→names[] {NATREC a a₁ a₂} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))
¬Names→names[] {PI a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {LAMBDA a} nn = ¬Names→names[] {a} nn
¬Names→names[] {APPLY a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {FIX a} nn = ¬Names→names[] {a} nn
¬Names→names[] {LET a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {WT a a₁ a₂} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))
¬Names→names[] {SUP a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {WREC a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {MT a a₁ a₂} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))
¬Names→names[] {SUM a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {PAIR a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {SPREAD a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {SET a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {TUNION a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {ISECT a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {UNION a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {INL a} nn = ¬Names→names[] {a} nn
¬Names→names[] {INR a} nn = ¬Names→names[] {a} nn
¬Names→names[] {DECIDE a a₁ a₂} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))
¬Names→names[] {EQ a a₁ a₂} nn =
  →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn))
    (→++≡[] (¬Names→names[] (∧≡true→ₗ _ _ (∧≡true→ᵣ _ _ nn))) (¬Names→names[] (∧≡true→ᵣ _ _ (∧≡true→ᵣ _ _ nn))))
¬Names→names[] {AX} nn = refl
¬Names→names[] {FREE} nn = refl
¬Names→names[] {CHOOSE a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {MSEQ x} nn = refl
¬Names→names[] {MAPP x a} nn = ¬Names→names[] {a} nn
¬Names→names[] {NOWRITE} nn = refl
¬Names→names[] {NOREAD} nn = refl
¬Names→names[] {SUBSING a} nn = ¬Names→names[] {a} nn
¬Names→names[] {PARTIAL a} nn = ¬Names→names[] {a} nn
¬Names→names[] {FFDEFS a a₁} nn = →++≡[] (¬Names→names[] (∧≡true→ₗ _ _ nn)) (¬Names→names[] (∧≡true→ᵣ _ _ nn))
¬Names→names[] {PURE} nn = refl
¬Names→names[] {NOSEQ} nn = refl
¬Names→names[] {NOENC} nn = refl
¬Names→names[] {TERM a} nn = ¬Names→names[] {a} nn
¬Names→names[] {ENC a} nn = ¬Names→names[] {a} nn
¬Names→names[] {UNIV x} nn = refl
¬Names→names[] {LIFT a} nn = ¬Names→names[] {a} nn
¬Names→names[] {LOWER a} nn = ¬Names→names[] {a} nn
¬Names→names[] {SHRINK a} nn = ¬Names→names[] {a} nn


++2≡[]→₁ : {A : Set} {l k : List A} → l ++ k ≡ [] → l ≡ []
++2≡[]→₁ {A} {[]} {k} h = refl


++2≡[]→₂ : {A : Set} {l k : List A} → l ++ k ≡ [] → k ≡ []
++2≡[]→₂ {A} {[]} {k} h = h


++3≡[]→₁ : {A : Set} {l k j : List A} → l ++ k ++ j ≡ [] → l ≡ []
++3≡[]→₁ {A} {l} {k} {j} h = ++2≡[]→₁ {A} {l} {k ++ j} h


++3≡[]→₂ : {A : Set} {l k j : List A} → l ++ k ++ j ≡ [] → k ≡ []
++3≡[]→₂ {A} {l} {k} {j} h = ++2≡[]→₁ (++2≡[]→₂ {A} {l} {k ++ j} h)


++3≡[]→₃ : {A : Set} {l k j : List A} → l ++ k ++ j ≡ [] → j ≡ []
++3≡[]→₃ {A} {l} {k} {j} h = ++2≡[]→₂ (++2≡[]→₂ {A} {l} {k ++ j} h)


++4≡[]→₁ : {A : Set} {l k j i : List A} → l ++ k ++ j ++ i ≡ [] → l ≡ []
++4≡[]→₁ {A} {l} {k} {j} {i} h = ++3≡[]→₁ {A} {l} {k} {j ++ i} h


++4≡[]→₂ : {A : Set} {l k j i : List A} → l ++ k ++ j ++ i ≡ [] → k ≡ []
++4≡[]→₂ {A} {l} {k} {j} {i} h = ++3≡[]→₂ {A} {l} {k} {j ++ i} h


++4≡[]→₃ : {A : Set} {l k j i : List A} → l ++ k ++ j ++ i ≡ [] → j ≡ []
++4≡[]→₃ {A} {l} {k} {j} {i} h = ++2≡[]→₁ (++3≡[]→₃ {A} {l} {k} {j ++ i} h)


++4≡[]→₄ : {A : Set} {l k j i : List A} → l ++ k ++ j ++ i ≡ [] → i ≡ []
++4≡[]→₄ {A} {l} {k} {j} {i} h = ++2≡[]→₂ (++3≡[]→₃ {A} {l} {k} {j ++ i} h)


⇛!→¬Names : (w : 𝕎·) (t u : Term)
          → t ⇛! u at w
          → ¬Names t
          → ¬Names u
⇛!→¬Names w t u comp nn =
  steps→¬Names (fst (lower (comp w (⊑-refl· w)))) w w t u (snd (lower (comp w (⊑-refl· w)))) nn


presPure : (a b : Term) → Set
presPure a b =
    (¬Names a → ¬Names b)
  × (¬Seq   a → ¬Seq   b)
  × (¬Enc   a → ¬Enc   b)


→presPure-NATREC₁ : {a b c : Term}
                  → ¬Names b
                  → ¬Names c
                  → ¬Seq b
                  → ¬Seq c
                  → ¬Enc b
                  → ¬Enc c
                  → presPure a (NATREC a b c)
→presPure-NATREC₁ {a} {b} {c} nnb nnc nsb nsc neb nec =
  (λ z → →∧≡true z (→∧≡true nnb nnc)) ,
  (λ z → →∧≡true z (→∧≡true nsb nsc)) ,
  (λ z → →∧≡true z (→∧≡true neb nec))


→presPure-NATREC₂ : {a b c : Term}
                  → ¬Names a
                  → ¬Names c
                  → ¬Seq a
                  → ¬Seq c
                  → ¬Enc a
                  → ¬Enc c
                  → presPure b (NATREC a b c)
→presPure-NATREC₂ {a} {b} {c} nna nnc nsa nsc nea nec =
  (λ z → →∧≡true nna (→∧≡true z nnc)) ,
  (λ z → →∧≡true nsa (→∧≡true z nsc)) ,
  (λ z → →∧≡true nea (→∧≡true z nec))


→presPure-NATREC₃ : {a b c : Term}
                  → ¬Names a
                  → ¬Names b
                  → ¬Seq a
                  → ¬Seq b
                  → ¬Enc a
                  → ¬Enc b
                  → presPure c (NATREC a b c)
→presPure-NATREC₃ {a} {b} {c} nna nnb nsa nsb nea neb =
  (λ z → →∧≡true nna (→∧≡true nnb z)) ,
  (λ z → →∧≡true nsa (→∧≡true nsb z)) ,
  (λ z → →∧≡true nea (→∧≡true neb z))


_⇛ₚ_at_ : (T T' : Term) (w : 𝕎·) → Set(lsuc(L))
T ⇛ₚ T' at w =
  T ⇛! T' at w
--  × presPure T' T
infix 30 _⇛ₚ_at_


_#⇛ₚ_at_ : (T T' : CTerm) (w : 𝕎·) → Set(lsuc(L))
T #⇛ₚ T' at w =
  T #⇛! T' at w
--  × presPure ⌜ T' ⌝ ⌜ T ⌝
infix 30 _#⇛ₚ_at_


⇛ₚ-mon : {a b : Term} {w1 w2 : 𝕎·}
       → w1 ⊑· w2
       → a ⇛ₚ b at w1
       → a ⇛ₚ b at w2
⇛ₚ-mon {a} {b} {w1} {w2} e (comp {-- , conds--}) =
  ∀𝕎-mon e comp -- , conds


equalTerms-#⇛ₚ-left-rev-at : ℕ → Set(lsuc(L))
equalTerms-#⇛ₚ-left-rev-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛ₚ b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt b c
  → equalTerms i w eqt a c


{--
#⇛ₚ→#¬Names : {w : 𝕎·} {a b : CTerm}
            → b #⇛ₚ a at w
            → #¬Names a
            → #¬Names b
#⇛ₚ→#¬Names {w} {a} {b} (comp , nn , ns , ne) na = nn na


#⇛ₚ→#¬Seq : {w : 𝕎·} {a b : CTerm}
            → b #⇛ₚ a at w
            → #¬Seq a
            → #¬Seq b
#⇛ₚ→#¬Seq {w} {a} {b} (comp , nn , ns , ne) na = ns na


#⇛ₚ→#¬Enc : {w : 𝕎·} {a b : CTerm}
            → b #⇛ₚ a at w
            → #¬Enc a
            → #¬Enc b
#⇛ₚ→#¬Enc {w} {a} {b} (comp , nn , ns , ne) na = ne na
--}


#⇛ₚ-pres-#⇛!ₙ : (w : 𝕎·) (a b : CTerm)
              → b #⇛ₚ a at w
              → #⇛!ₙ a w
              → #⇛!ₙ b w
#⇛ₚ-pres-#⇛!ₙ w a b (comp {-- , pp--}) (c , h , cond) =
  c , #⇛!-trans {w} {b} {a} {c} comp h , cond


#⇛ₚ-pres-#⇛!ₛ : (w : 𝕎·) (a b : CTerm)
              → b #⇛ₚ a at w
              → #⇛!ₛ a w
              → #⇛!ₛ b w
#⇛ₚ-pres-#⇛!ₛ w a b (comp {-- , pp--}) (c , h , cond) =
  c , #⇛!-trans {w} {b} {a} {c} comp h , cond


#⇛ₚ-pres-#⇛!ₑ : (w : 𝕎·) (a b : CTerm)
              → b #⇛ₚ a at w
              → #⇛!ₑ a w
              → #⇛!ₑ b w
#⇛ₚ-pres-#⇛!ₑ w a b (comp {-- , pp--}) (c , h , cond) =
  c , #⇛!-trans {w} {b} {a} {c} comp h , cond


#⇛ₚ→#⇛ : {w : 𝕎·} {a b : CTerm}
       → b #⇛ₚ a at w
       → b #⇛ a at w
#⇛ₚ→#⇛ {w} {a} {b} (comp {-- , nn--}) = #⇛!→#⇛ comp


#⇛ₚ-pres-⇓sameℕ : {w : 𝕎·} {a b c : Term}
                → b ⇛ₚ a at w
                → ⇓sameℕ w a c
                → ⇓sameℕ w b c
#⇛ₚ-pres-⇓sameℕ {w} {a} {b} {c} (comp {-- , conds--}) (k , c₁ , c₂) =
  k , ⇓-trans₁ {w} {w} {b} {a} {NUM k} (lower (comp w (⊑-refl· w))) c₁ , c₂


#⇛ₚ-pres-QNATeq : {w : 𝕎·} {a b c : CTerm}
                → b #⇛ₚ a at w
                → QNATeq w a c
                → QNATeq w b c
#⇛ₚ-pres-QNATeq {w} {a} {b} {c} comp e w1 e1 =
  lift (#⇛ₚ-pres-⇓sameℕ (⇛ₚ-mon e1 comp) (lower (e w1 e1)))


#⇛ₚ-pres-FREEeq : {w : 𝕎·} {a b c : CTerm}
                → b #⇛ₚ a at w
                → FREEeq w a c
                → FREEeq w b c
#⇛ₚ-pres-FREEeq {w} {a} {b} {c} comp (n , c₁ , c₂) =
  n , ⇛-trans {w} {⌜ b ⌝} {⌜ a ⌝} {CS n} (#⇛!→#⇛ ({--fst--} comp)) c₁ , c₂


pres-#¬Names-APPLY : {a b c : CTerm}
                   → (#¬Names a → #¬Names b)
                   → (#¬Names (#APPLY a c) → #¬Names (#APPLY b c))
pres-#¬Names-APPLY {a} {b} {c} i na =
  →∧≡true (i (∧≡true→ₗ _ _ na)) (∧≡true→ᵣ _ _ na)


pres-#¬Seq-APPLY : {a b c : CTerm}
                 → (#¬Seq a → #¬Seq b)
                 → (#¬Seq (#APPLY a c) → #¬Seq (#APPLY b c))
pres-#¬Seq-APPLY {a} {b} {c} i na =
  →∧≡true (i (∧≡true→ₗ _ _ na)) (∧≡true→ᵣ _ _ na)


pres-#¬Enc-APPLY : {a b c : CTerm}
                 → (#¬Enc a → #¬Enc b)
                 → (#¬Enc (#APPLY a c) → #¬Enc (#APPLY b c))
pres-#¬Enc-APPLY {a} {b} {c} i na =
  →∧≡true (i (∧≡true→ₗ _ _ na)) (∧≡true→ᵣ _ _ na)


#⇛ₚ-pres-APPLY : {b a c : CTerm} {w : 𝕎·}
               → b #⇛ₚ a at w
               → #APPLY b c #⇛ₚ #APPLY a c at w
#⇛ₚ-pres-APPLY {b} {a} {c} {w} (comp {-- , nn , ns , ne--}) =
  →-#⇛!-#APPLY {w} {b} {a} c comp {--,
  pres-#¬Names-APPLY {a} {b} {c} nn ,
  pres-#¬Seq-APPLY   {a} {b} {c} ns ,
  pres-#¬Enc-APPLY   {a} {b} {c} ne
--}


#⇛!-pres-#⇓→#⇛-rev : {w : 𝕎·} {a b : CTerm}
                    → b #⇛! a at w
                    → #⇓→#⇛ w a
                    → #⇓→#⇛ w b
#⇛!-pres-#⇓→#⇛-rev {w} {a} {b} comp h w1 e1 v isv cv =
  ⇛-trans {w1} {⌜ b ⌝} {⌜ a ⌝} {⌜ v ⌝} (#⇛!→#⇛ (∀𝕎-mon e1 comp))
    (h w1 e1 v isv (val-⇓→ {w1} {w1} {⌜ b ⌝} {⌜ a ⌝} {⌜ v ⌝} isv (lower (comp w1 e1)) cv))


#⇛ₚ-refl : {w : 𝕎·} {t : CTerm} → t #⇛ₚ t at w
#⇛ₚ-refl {w} {t} = #⇛!-refl {-- , (λ z → z) , (λ z → z) , (λ z → z)--}


TUNION-eq-#⇛ₚ-rev : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c d : CTerm}
                  → (cb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b c : CTerm} → a #⇛ₚ b at w → eqb a₁ a₂ ea b c → eqb a₁ a₂ ea a c)
                  → (sb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b : CTerm} → eqb a₁ a₂ ea a b → eqb a₁ a₂ ea b a)
                  → a #⇛ₚ b at w
                  → c #⇛ₚ d at w
                  → TUNION-eq eqa eqb b d
                  → TUNION-eq eqa eqb a c
TUNION-eq-#⇛ₚ-rev {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ (TUNION-eq-base a1 a2 ea eb) =
  TUNION-eq-base a1 a2 ea (cb c₁ (sb (cb c₂ (sb eb))))
TUNION-eq-#⇛ₚ-rev {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ (TUNION-eq-trans t h1 h2) =
  TUNION-eq-trans
    t
    (TUNION-eq-#⇛ₚ-rev cb sb c₁ (#⇛ₚ-refl {w} {t}) h1)
    (TUNION-eq-#⇛ₚ-rev cb sb (#⇛ₚ-refl {w} {t}) c₂ h2)


TUNIONeq-#⇛ₚ-rev : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c d : CTerm}
                 → (cb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b c : CTerm} → a #⇛ₚ b at w → eqb a₁ a₂ ea b c → eqb a₁ a₂ ea a c)
                 → (sb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b : CTerm} → eqb a₁ a₂ ea a b → eqb a₁ a₂ ea b a)
                 → a #⇛ₚ b at w
                 → c #⇛ₚ d at w
                 → TUNIONeq eqa eqb b d
                 → TUNIONeq eqa eqb a c
TUNIONeq-#⇛ₚ-rev {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ h =
  TUNION-eq→ (TUNION-eq-#⇛ₚ-rev cb sb c₁ c₂ (→TUNION-eq h))


#⇛ₚ-pres-weq-L : {w : 𝕎·} {a b c : CTerm}
                  {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {eqc : per}
                  → b #⇛ₚ a at w
                  → (eqc a c → eqc b c)
                  → weq eqa eqb eqc w a c
                  → weq eqa eqb eqc w b c
#⇛ₚ-pres-weq-L {w} {a} {b} {c} {eqa} {eqb} {eqc} comp indc (weqC a1 f1 a2 f2 e x x₁ z x₂) =
  weqC a1 f1 a2 f2 e (⇓-trans₁ {w} {w} {⌜ b ⌝} {⌜ a ⌝} {⌜ #SUP a1 f1 ⌝} (lower ({--fst--} comp w (⊑-refl· w))) x) x₁ (indc z) x₂


#⇛ₚ-pres-meq-L : {w : 𝕎·} {a b c : CTerm}
                 {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {eqc : per}
               → b #⇛ₚ a at w
               → (eqc a c → eqc b c)
               → meq eqa eqb eqc w a c
               → meq eqa eqb eqc w b c
meq.meqC (#⇛ₚ-pres-meq-L {w} {a} {b} {c} {eqa} {eqb} {eqc} comp indc h) with meq.meqC h
... | (a1 , f1 , a2 , f2 , e , x , x₁ , z , x₂) =
  a1 , f1 , a2 , f2 , e ,
  ⇓-trans₁ {w} {w} {⌜ b ⌝} {⌜ a ⌝} {⌜ #SUP a1 f1 ⌝} (lower ({--fst--} comp w (⊑-refl· w))) x ,
  x₁ , indc z , x₂


abstract
  equalTerms-#⇛ₚ-left-rev-aux : {i : ℕ}
                              → (uind : (j : ℕ) → j < i → equalTerms-#⇛ₚ-left-rev-at j)
                              → equalTerms-#⇛ₚ-left-rev-at i
  equalTerms-#⇛ₚ-left-rev-aux {i} uind {w} {A} {B} {b} {a} {c} comp eqt eqi = concl uind b comp
    where
      ind : {u : ℕ} {w : 𝕎·} {A B : CTerm} (eqt : equalTypes u w A B) {a c : CTerm} (eqi : equalTerms u w eqt a c)
            → ({u' : ℕ} {w' : 𝕎·} {A' B' : CTerm} (eqt' : equalTypes u' w' A' B') {a' c' : CTerm} (eqi' : equalTerms u' w' eqt' a' c')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → ((j : ℕ) → j < u' → equalTerms-#⇛ₚ-left-rev-at j)
                → (b' : CTerm) → b' #⇛ₚ a' at w' → equalTerms u' w' eqt' b' c')
            → ((j : ℕ) → j < u → equalTerms-#⇛ₚ-left-rev-at j)
            → (b : CTerm) → b #⇛ₚ a at w → equalTerms u w eqt b c
      ind {i} {w} {A} {B} (EQTQNAT x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛ₚ-pres-QNATeq (⇛ₚ-mon e1 comp) h) eqi
      ind {i} {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
      ind {i} {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
      ind {i} {w} {A} {B} (EQTFREE x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛ₚ-pres-FREEeq (⇛ₚ-mon e1 comp) h) eqi
      ind {i} {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                             → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
          aw w' e h a₁ a₂ ea =
            ind {i} {w'} {sub0 a₁ B1} {sub0 a₂ B2} (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
              (<Type1 _ _ (<TypePIb (ℕ→𝕌 i) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w' e a₁ a₂ ea))
              uind _ (#⇛ₚ-pres-APPLY (⇛ₚ-mon e comp))
      ind {i} {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c
                             → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c)
          aw w' e (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) =
            a₁ , a₂ , b₁ , b₂ , ea ,
            ⇓-trans₁ {w'} {w'} {⌜ b ⌝} {⌜ a ⌝} {⌜ #PAIR a₁ b₁ ⌝} (lower ({--fst--} comp w' e)) c₁ ,
            c₂ , eb
      ind {i} {w} {A} {B} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → weq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) (equalTerms i w' (eqtc w' e')) w' a c
                             → weq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) (equalTerms i w' (eqtc w' e')) w' b c)
          aw w' e h =
            #⇛ₚ-pres-weq-L {w'} {a} {b} {c} (⇛ₚ-mon e comp)
              (λ z → ind {i} {w'} {C1} {C2} (eqtc w' e) {a} {c} z
                       (<Type1 _ _ (<TypeWc (ℕ→𝕌 i) w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc w' e))
                       uind b (⇛ₚ-mon e comp))
              h
      ind {i} {w} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → meq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) (equalTerms i w' (eqtc w' e')) w' a c
                             → meq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) (equalTerms i w' (eqtc w' e')) w' b c)
          aw w' e h =
            #⇛ₚ-pres-meq-L {w'} {a} {b} {c} (⇛ₚ-mon e comp)
              (λ z → ind {i} {w'} {C1} {C2} (eqtc w' e) {a} {c} z
                       (<Type1 _ _ (<TypeMc (ℕ→𝕌 i) w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc w' e))
                       uind b (⇛ₚ-mon e comp))
              h
      ind {i} {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                             → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
          aw w' e (y , ea , eb) =
            y ,
            ind {i} {w'} {A1} {A2} (eqta w' e) ea
              (<Type1 _ _ (<TypeSETa (ℕ→𝕌 i) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w' e))
              uind _ (⇛ₚ-mon e comp) ,
            eqInType-extr1 (sub0 c B2) (sub0 b B1) (eqtb w' e a c ea)
              (eqtb w' e b c (ind {i} {w'} {A1} {A2} (eqta w' e) ea
                (<Type1 _ _ (<TypeSETa (ℕ→𝕌 i) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w' e))
                uind _ (⇛ₚ-mon e comp))) eb
      ind {i} {w} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → ISECTeq (equalTerms i w' (eqta w' e')) (equalTerms i w' (eqtb w' e')) a c
                             → ISECTeq (equalTerms i w' (eqta w' e')) (equalTerms i w' (eqtb w' e')) b c)
          aw w' e (h1 , h2) =
            ind {i} {w'} {A1} {A2} (eqta w' e) h1
              (<Type1 _ _ (<TypeISECTl (ℕ→𝕌 i) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w' e))
              uind _ (⇛ₚ-mon e comp) ,
            ind {i} {w'} {B1} {B2} (eqtb w' e) h2
              (<Type1 _ _ (<TypeISECTr (ℕ→𝕌 i) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w' e))
              uind _ (⇛ₚ-mon e comp)
      ind {i} {w} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                             → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
          aw w' e h =
            TUNIONeq-#⇛ₚ-rev
              (λ {a₁} {a₂} {ea} {x0} {y} {z} cw j → ind {i} {w'} {sub0 a₁ B1} {sub0 a₂ B2}
                (eqtb w' e a₁ a₂ ea) {y} {z} j
                  (<Type1 _ _ (<TypeTUNIONb (ℕ→𝕌 i) w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb w' e a₁ a₂ ea))
                  uind _ cw)
              (λ {a₁} {a₂} {ea} {x} {y} j → eqInType-sym (eqtb w' e a₁ a₂ ea) j)
              (⇛ₚ-mon e comp)
              (#⇛ₚ-refl {w'} {c})
              h
      ind {i} {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' a c
                             → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' b c)
          aw w' e ea = ea
      ind {i} {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c
                             → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c)
          aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) =
            a₁ , a₂ , inj₁ (⇓-trans₁ {w'} {w'} {⌜ b ⌝} {⌜ a ⌝} {⌜ #INL a₁ ⌝} (lower ({--fst--} comp w' e)) c₁ ,
                            c₂ , ea)
          aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) =
            a₁ , a₂ , inj₂ (⇓-trans₁ {w'} {w'} {⌜ b ⌝} {⌜ a ⌝} {⌜ #INR a₁ ⌝} (lower ({--fst--} comp w' e)) c₁ ,
                            c₂ , ea)
      ind {i} {w} {A} {B} (EQTNOWRITE x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → NOWRITEeq w' a c
                             → NOWRITEeq w' b c)
          aw w' e (c₁ , c₂) = #⇛!-pres-#⇓→#⇓!-rev {w'} {a} {b} ({--fst--} (⇛ₚ-mon e comp)) c₁ , c₂
      ind {i} {w} {A} {B} (EQTNOREAD x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → NOREADeq w' a c
                             → NOREADeq w' b c)
          aw w' e (c₁ , c₂) = #⇛!-pres-#⇓→#⇛-rev {w'} {a} {b} ({--fst--} (⇛ₚ-mon e comp)) c₁ , c₂
      ind {i} {w} {A} {B} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalTerms i w' (eqtA w' e')) a c
                             → SUBSINGeq (equalTerms i w' (eqtA w' e')) b c)
          aw w' e (h , q) =
            ind
              {i} {w'} {A1} {A2} (eqtA w' e) {a} {b}
              (eqInType-sym
                (eqtA w' e)
                (ind {i} {w'} {A1} {A2} (eqtA w' e) {a} {a} h
                  (<Type1 _ _ (<TypeSUBSING (ℕ→𝕌 i) w A B A1 A2 x x₁ eqtA exta w' e))
                  uind _ (⇛ₚ-mon e comp)))
              (<Type1 _ _ (<TypeSUBSING (ℕ→𝕌 i) w A B A1 A2 x x₁ eqtA exta w' e)) uind _ (⇛ₚ-mon e comp) ,
            q
      ind {i} {w} {A} {B} (EQTPARTIAL A1 A2 x x₁ eqtA exta) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → PARTIALeq (equalTerms i w' (eqtA w' e')) w' a c
                             → PARTIALeq (equalTerms i w' (eqtA w' e')) w' b c)
          aw w' e h w1 e1 with h w1 e1
          ... | h1 , h2 , h3 =
            (λ q → h1 (#⇛!-pres-hasValue {w1} {b} {a} (∀𝕎-mon (⊑-trans· e e1) comp) q)) ,
            (λ q → #⇛!-pres-hasValue-rev {w1} {b} {a} (∀𝕎-mon (⊑-trans· e e1) comp) (h2 q)) ,
            λ q → ind
              {i} {w'} {A1} {A2} (eqtA w' e) {a} {c}
              (h3 (#⇛!-pres-hasValue {w1} {b} {a} (∀𝕎-mon (⊑-trans· e e1) comp) q))
              (<Type1 _ _ (<TypePARTIAL (ℕ→𝕌 i) w A B A1 A2 x x₁ eqtA exta w' e)) uind _ (⇛ₚ-mon e comp)
      ind {i} {w} {A} {B} (EQTPURE x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → PUREeq w' a c
                             → PUREeq w' b c)
          aw w' e (y₁ , y₂) = #⇛ₚ-pres-#⇛!ₙ w' a b (⇛ₚ-mon e comp) y₁ , y₂ --lift (#⇛ₚ→#¬Names comp y₁ , y₂)
      ind {i} {w} {A} {B} (EQTNOSEQ x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → NOSEQeq w' a c
                             → NOSEQeq w' b c)
          aw w' e (y₁ , y₂) = #⇛ₚ-pres-#⇛!ₛ w' a b (⇛ₚ-mon e comp) y₁ , y₂ --lift (#⇛ₚ→#¬Seq comp y₁ , y₂)
      ind {i} {w} {A} {B} (EQTNOENC x x₁) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → NOENCeq w' a c
                             → NOENCeq w' b c)
          aw w' e (y₁ , y₂) = #⇛ₚ-pres-#⇛!ₑ w' a b (⇛ₚ-mon e comp) y₁ , y₂ --lift (#⇛ₚ→#¬Enc comp y₁ , y₂)
      ind {i} {w} {A} {B} (EQTTERM t1 t2 x x₁ x₂) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M (λ w1 e1 z → z) eqi
      ind {i} {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a} {c} eqi ind uind b comp =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a c
                             → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' b c)
          aw w' e y = y
      ind {i} {w} {A} {B} (EQTUNIV i₁ p x x₁) {a} {c} eqi ind uind b comp =
        □·EqTypes→uniUpTo {i₁} {i} {p} (Mod.∀𝕎-□Func M aw (uniUpTo→□·EqTypes {i₁} {i} {p} eqi))
        where
          aw : ∀𝕎 w (λ w' e' → equalTypes i₁ w' a c → equalTypes i₁ w' b c)
          aw w' e h = equalTypes-#⇛-left-rev (#⇛ₚ→#⇛ (⇛ₚ-mon e comp)) h
      ind {i} {w} {A} {B} (EQTBAR x) {a} {c} eqi ind uind b comp =
        □'-change W M x x aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : equalTypes i w' A B) (at₁ : at□· x w' e' x₁) (at₂ : at□· x w' e' x₂)
                             → equalTerms i w' x₁ a c → equalTerms i w' x₂ b c)
          aw w' e x₁ x₂ at₁ at₂ h =
            ind {i} {w'} {A} {B} x₂ {a} {c}
              (eqInType-extl1 B B x₁ x₂ h)
              (<Type1 x₂ (EQTBAR x) (<TypeBAR (ℕ→𝕌 i) w A B x w' e x₂ at₂))
              uind _ (⇛ₚ-mon e comp)

      concl : ((j : ℕ) → j < i → equalTerms-#⇛ₚ-left-rev-at j)
            → (b : CTerm) → b #⇛ₚ a at w → equalTerms i w eqt b c
      concl uind b comp =
        equalTerms-ind
          (λ {i} {w} {A} {B} eqt {a} {c} eqi → ((j : ℕ) → j < i → equalTerms-#⇛ₚ-left-rev-at j)
                                             → (b : CTerm) → b #⇛ₚ a at w → equalTerms i w eqt b c)
          ind eqt a c eqi uind b comp


equalTerms-#⇛ₚ-left-rev : (i : ℕ) → equalTerms-#⇛ₚ-left-rev-at i
equalTerms-#⇛ₚ-left-rev i = <ℕind equalTerms-#⇛ₚ-left-rev-at (λ n ind → equalTerms-#⇛ₚ-left-rev-aux ind) i


equalInType-#⇛ₚ-left-rev : {i : ℕ} {w : 𝕎·} {T a b c : CTerm}
                           → a #⇛ₚ b at w
                           → equalInType i w T b c
                           → equalInType i w T a c
equalInType-#⇛ₚ-left-rev {i} {w} {T} {a} {b} {c} comp (eqt , eqi) = eqt , equalTerms-#⇛ₚ-left-rev i comp eqt eqi


equalInType-#⇛ₚ-left-right-rev : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                               → a #⇛ₚ b at w
                               → c #⇛ₚ d at w
                               → equalInType i w T b d
                               → equalInType i w T a c
equalInType-#⇛ₚ-left-right-rev {i} {w} {T} {a} {b} {c} {d} c₁ c₂ a∈ =
  equalInType-#⇛ₚ-left-rev c₁ (equalInType-sym (equalInType-#⇛ₚ-left-rev c₂ (equalInType-sym a∈)))


abstract
  equalTypesPI→ₗ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                 → equalTypes i w (#PI A B) (#PI C D)
                 → equalTypes i w A C
  equalTypesPI→ₗ {w} {i} {A} {B} {C} {D} eqt = concl (#PI A B) (#PI C D) eqt refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → T1' ≡ #PI A B → T2' ≡ #PI C D → equalTypes u' w' A C)
            → T1 ≡ #PI A B → T2 ≡ #PI C D → equalTypes u w A C
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2
        = ≡CTerm→eqTypes
            (sym (#PIinj1 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#PI A B) T1 (sym eq1) tt)))))
            (sym (#PIinj1 {C} {D} {A2} {B2} (trans (sym eq2) (#compAllVal x₁ (≡→#isValue (#PI C D) T2 (sym eq2) tt)))))
            (eqta w (⊑-refl· w))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqQTUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNOWRITE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNOREAD (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPARTIAL A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqPARTIAL (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqNOENC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV m p c₁ c₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqUNIV (compAllVal c₁ tt))
--      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 =
        eqTypes-local (∀𝕎-□at W M x aw)
        where
        aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z → equalTypes u w' A C)
        aw w1 e1 z at = ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2)
              → T1 ≡ #PI A B → T2 ≡ #PI C D → equalTypes i w A C
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {i} {w} {T1} {T2} eqt → T1 ≡ #PI A B → T2 ≡ #PI C D → equalTypes i w A C)
          ind eqt



abstract
  equalTypesPI→ᵣ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                 → equalTypes i w (#PI A B) (#PI C D)
                 → (a b : CTerm)
                 → equalInType i w A a b
                 → equalTypes i w (sub0 a B) (sub0 b D)
  equalTypesPI→ᵣ {w} {i} {A} {B} {C} {D} eqt a b a∈ = concl (#PI A B) (#PI C D) eqt refl refl a∈
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → T1' ≡ #PI A B → T2' ≡ #PI C D → equalInType u' w' A a b → equalTypes u' w' (sub0 a B) (sub0 b D))
            → T1 ≡ #PI A B → T2 ≡ #PI C D → equalInType u w A a b → equalTypes u w (sub0 a B) (sub0 b D)
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈
        = ≡CTerm→eqTypes
            (→≡sub0 {a} (sym (#PIinj2 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#PI A B) T1 (sym eq1) tt))))))
            (→≡sub0 {b} (sym (#PIinj2 {C} {D} {A2} {B2} (trans (sym eq2) (#compAllVal x₁ (≡→#isValue (#PI C D) T2 (sym eq2) tt))))))
            (eqtb w (⊑-refl· w) a b
              (equalInType→eqInType {u} {w} {A} {A1} {A2}
                (#PIinj1 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#PI A B) T1 (sym eq1) tt))))
                a∈))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqQTUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqNOWRITE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqNOREAD (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPARTIAL A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqPARTIAL (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqNOENC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV m p c₁ c₂) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqUNIV (compAllVal c₁ tt))
--      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 a∈ =
        eqTypes-local (∀𝕎-□at W M x aw)
        where
        aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z
                           → equalTypes u w' (sub0 a B) (sub0 b D))
        aw w1 e1 z at = ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1 eq2
                            (equalInType-mon a∈ w1 e1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2)
              → T1 ≡ #PI A B → T2 ≡ #PI C D → equalInType i w A a b → equalTypes i w (sub0 a B) (sub0 b D)
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {i} {w} {T1} {T2} eqt → T1 ≡ #PI A B → T2 ≡ #PI C D → equalInType i w A a b → equalTypes i w (sub0 a B) (sub0 b D))
          ind eqt


eqTypesSUM!← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
             → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
             → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
             → equalTypes i w (#SUM! A B) (#SUM! C D)
eqTypesSUM!← {w} {i} {A} {B} {C} {D} eqta eqtb =
  eqTypesNOWRITEMOD← (eqTypesNOREADMOD← (eqTypesSUM← eqta eqtb))


eqTypesUNION!← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
               → equalTypes i w A C
               → equalTypes i w B D
               → equalTypes i w (#UNION! A B) (#UNION! C D)
eqTypesUNION!← {w} {i} {A} {B} {C} {D} eqta eqtb =
  eqTypesNOWRITEMOD← (eqTypesNOREADMOD← (eqTypesUNION← eqta eqtb))


SUMeq! : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → wper
SUMeq! eqa eqb w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    Σ (eqa a1 a2) (λ ea →
    f #⇛! (#PAIR a1 b1) at w
    × g #⇛! (#PAIR a2 b2) at w
    × eqb a1 a2 ea b1 b2)))))


UNIONeq! : (eqa eqb : per) → wper
UNIONeq! eqa eqb w t₁ t₂ =
  Σ CTerm (λ a → Σ CTerm (λ b →
    (t₁ #⇛! (#INL a) at w × t₂ #⇛! (#INL b) at w × eqa a b)
    ⊎
    (t₁ #⇛! (#INR a) at w × t₂ #⇛! (#INR b) at w × eqb a b)))


noread→#⇛ : {w : 𝕎·} {t v : CTerm}
          → #isValue v
          → #⇓→#⇛ w t
          → t #⇓ v at w
          → t #⇛ v at w
noread→#⇛ {w} {t} {v} isv nor comp = nor w (⊑-refl· w) v isv comp


noread-nowrite→#⇛! : {w : 𝕎·} {t v : CTerm}
                   → #isValue v
                   → #⇓→#⇛ w t
                   → #⇓→#⇓! w t
                   → t #⇓ v at w
                   → t #⇛! v at w
noread-nowrite→#⇛! {w} {t} {v} isv nor now comp =
  #⇛→#⇛! {w} {t} {v} now isv c
  where
  c : t #⇛ v at w
  c = noread→#⇛ isv nor comp


abstract
  equalInType-SUM!→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                    → equalInType u w (#SUM! A B) f g
                    → □· w (λ w' _ → SUMeq! (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
  equalInType-SUM!→ {u} {w} {A} {B} {f} {g} f∈ =
    Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInTypeNOWRITEMOD→ f∈))
    where
    aw1 : ∀𝕎 w (λ w' e' → NOWRITEMODeq (equalInType u w' (#NOREADMOD (#SUM A B))) w' f g
                        → □· w' (↑wPred' (λ w'' _ → SUMeq! (equalInType u w'' A)
                                                           (λ a b ea → equalInType u w'' (sub0 a B)) w'' f g) e'))
    aw1 w1 e1 (f∈1 , (c₁ , c₂)) = Mod.□-idem M (Mod.∀𝕎-□Func M aw2 (equalInTypeNOREADMOD→ f∈1))
      where
      aw2 : ∀𝕎 w1 (λ w' e' → NOREADMODeq (equalInType u w' (#SUM A B)) w' f g
                           → □· w' (↑wPred' (↑wPred' (λ w'' _ → SUMeq! (equalInType u w'' A)
                                                                       (λ a b ea → equalInType u w'' (sub0 a B)) w'' f g) e1) e'))
      aw2 w2 e2 (f∈2 , (d₁ , d₂)) = Mod.∀𝕎-□Func M aw3 (equalInType-SUM→ f∈2)
        where
        aw3 : ∀𝕎 w2 (λ w' e' → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g
                             → ↑wPred' (↑wPred' (λ w'' _ → SUMeq! (equalInType u w'' A)
                                                                  (λ a b ea → equalInType u w'' (sub0 a B)) w'' f g) e1) e2 w' e')
        aw3 w3 e3 (a₁ , a₂ , b₁ , b₂ , a∈ , p₁ , p₂ , b∈) z₁ z₂ =
          a₁ , a₂ , b₁ , b₂ , a∈ ,
          noread-nowrite→#⇛! tt (∀𝕎-mon e3 d₁) (∀𝕎-mon (⊑-trans· e2 e3) c₁) p₁ ,
          noread-nowrite→#⇛! tt (∀𝕎-mon e3 d₂) (∀𝕎-mon (⊑-trans· e2 e3) c₂) p₂ ,
          b∈


abstract
  equalInType-SUM! : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                   → ∀𝕎 w (λ w' _ → isType u w' A)
                   → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                   → □· w (λ w' _ → SUMeq! (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
                   → equalInType u w (#SUM! A B) f g
  equalInType-SUM! {u} {w} {A} {B} {f} {g} ha hb eqi =
    →equalInTypeNOWRITEMOD (Mod.∀𝕎-□Func M aw1 eqi)
    where
    aw1 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g
                        → equalInType u w' (#NOREADMOD (#SUM A B)) f g × NOWRITEeq w' f g)
    aw1 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
      →equalInTypeNOREADMOD (Mod.∀𝕎-□ M aw2) ,
      #⇛!-pres-#⇓→#⇓!-rev c₁ (#⇓→#⇓!-val w1 (#PAIR a₁ b₁) tt) ,
      #⇛!-pres-#⇓→#⇓!-rev c₂ (#⇓→#⇓!-val w1 (#PAIR a₂ b₂) tt)
        where
        aw2 : ∀𝕎 w1 (λ w' _ → equalInType u w' (#SUM A B) f g × NOREADeq w' f g)
        aw2 w2 e2 =
          equalInType-SUM
            (∀𝕎-mon (⊑-trans· e1 e2) ha)
            (∀𝕎-mon (⊑-trans· e1 e2) hb)
            (Mod.∀𝕎-□ M aw3) ,
          #⇛val→#⇓→#⇛ {w2} {f} {#PAIR a₁ b₁} tt (#⇛!→#⇛ (∀𝕎-mon e2 c₁)) ,
          #⇛val→#⇓→#⇛ {w2} {g} {#PAIR a₂ b₂} tt (#⇛!→#⇛ (∀𝕎-mon e2 c₂))
            where
            aw3 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) w' f g)
            aw3 w3 e3 =
              a₁ , a₂ , b₁ , b₂ ,
              equalInType-mon a∈ w3 (⊑-trans· e2 e3) ,
              #⇓!→#⇓ (lower (c₁ w3 (⊑-trans· e2 e3))) ,
              #⇓!→#⇓ (lower (c₂ w3 (⊑-trans· e2 e3))) ,
              equalInType-mon b∈ w3 (⊑-trans· e2 e3)


abstract
  equalTypesSUM→ₗ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                 → equalTypes i w (#SUM A B) (#SUM C D)
                 → equalTypes i w A C
  equalTypesSUM→ₗ {w} {i} {A} {B} {C} {D} eqt = concl (#SUM A B) (#SUM C D) eqt refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → T1' ≡ #SUM A B → T2' ≡ #SUM C D → equalTypes u' w' A C)
            → T1 ≡ #SUM A B → T2 ≡ #SUM C D → equalTypes u w A C
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2
        = ≡CTerm→eqTypes
            (sym (#SUMinj1 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#SUM A B) T1 (sym eq1) tt)))))
            (sym (#SUMinj1 {C} {D} {A2} {B2} (trans (sym eq2) (#compAllVal x₁ (≡→#isValue (#SUM C D) T2 (sym eq2) tt)))))
            (eqta w (⊑-refl· w))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOWRITE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOREAD (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPARTIAL A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPARTIAL (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqNOENC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV m p c₁ c₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqUNIV (compAllVal c₁ tt))
--      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 =
        eqTypes-local (∀𝕎-□at W M x aw)
        where
        aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z → equalTypes u w' A C)
        aw w1 e1 z at = ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2)
              → T1 ≡ #SUM A B → T2 ≡ #SUM C D → equalTypes i w A C
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {i} {w} {T1} {T2} eqt → T1 ≡ #SUM A B → T2 ≡ #SUM C D → equalTypes i w A C)
          ind eqt


abstract
  equalTypesSUM→ᵣ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                 → equalTypes i w (#SUM A B) (#SUM C D)
                 → (a b : CTerm)
                 → equalInType i w A a b
                 → equalTypes i w (sub0 a B) (sub0 b D)
  equalTypesSUM→ᵣ {w} {i} {A} {B} {C} {D} eqt a b a∈ = concl (#SUM A B) (#SUM C D) eqt refl refl a∈
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → T1' ≡ #SUM A B → T2' ≡ #SUM C D → equalInType u' w' A a b → equalTypes u' w' (sub0 a B) (sub0 b D))
            → T1 ≡ #SUM A B → T2 ≡ #SUM C D → equalInType u w A a b → equalTypes u w (sub0 a B) (sub0 b D)
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqQNAT (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈
        = ≡CTerm→eqTypes
            (→≡sub0 {a} (sym (#SUMinj2 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#SUM A B) T1 (sym eq1) tt))))))
            (→≡sub0 {b} (sym (#SUMinj2 {C} {D} {A2} {B2} (trans (sym eq2) (#compAllVal x₁ (≡→#isValue (#SUM C D) T2 (sym eq2) tt))))))
            (eqtb w (⊑-refl· w) a b
              (equalInType→eqInType {u} {w} {A} {A1} {A2}
                (#SUMinj1 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x (≡→#isValue (#SUM A B) T1 (sym eq1) tt))))
                a∈))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqISECT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqQTUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqTSQUASH (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqNOWRITE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqNOREAD (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPARTIAL A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqPARTIAL (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqNOENC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV m p c₁ c₂) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqUNIV (compAllVal c₁ tt))
--      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 a∈ rewrite eq1 | eq2 = ⊥-elim (SUMneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 a∈ =
        eqTypes-local (∀𝕎-□at W M x aw)
        where
        aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z
                           → equalTypes u w' (sub0 a B) (sub0 b D))
        aw w1 e1 z at = ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1 eq2
                            (equalInType-mon a∈ w1 e1)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2)
              → T1 ≡ #SUM A B → T2 ≡ #SUM C D → equalInType i w A a b → equalTypes i w (sub0 a B) (sub0 b D)
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {i} {w} {T1} {T2} eqt → T1 ≡ #SUM A B → T2 ≡ #SUM C D → equalInType i w A a b → equalTypes i w (sub0 a B) (sub0 b D))
          ind eqt


abstract
  equalTypesISECT→ₗ : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                    → equalTypes i w (#ISECT A B) (#ISECT C D)
                    → equalTypes i w A C
  equalTypesISECT→ₗ {w} {i} {A} {B} {C} {D} eqt = concl (#ISECT A B) (#ISECT C D) eqt refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → T1' ≡ #ISECT A B → T2' ≡ #ISECT C D → equalTypes u' w' A C)
            → T1 ≡ #ISECT A B → T2 ≡ #ISECT C D → equalTypes u w A C
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqQNAT (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTNAT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqQLT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqFREE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqPI (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqSUM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqW (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqSET (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2
        = ≡CTerm→eqTypes
            (sym (#ISECTinj1 {A} {B} {A1} {B1} (trans (sym eq1) (#compAllVal x  (≡→#isValue (#ISECT A B) T1 (sym eq1) tt)))))
            (sym (#ISECTinj1 {C} {D} {A2} {B2} (trans (sym eq2) (#compAllVal x₁ (≡→#isValue (#ISECT C D) T2 (sym eq2) tt)))))
            (eqtA w (⊑-refl· w))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTUNION (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqQTUNION (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTSQUASH (compAllVal x₁ tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTTRUNC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNOWRITE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNOREAD (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqSUBSING (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPARTIAL A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqPARTIAL (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqPURE (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNOSEQ (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqNOENC (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqTERM (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqFFDEFS (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTUNIV m p c₁ c₂) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqUNIV (compAllVal c₁ tt))
--      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (ISECTneqLIFT (compAllVal x₁ tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) ind eq1 eq2 =
        eqTypes-local (∀𝕎-□at W M x aw)
        where
        aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z → equalTypes u w' A C)
        aw w1 e1 z at = ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) eq1 eq2

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2)
              → T1 ≡ #ISECT A B → T2 ≡ #ISECT C D → equalTypes i w A C
      concl T1 T2 eqt =
        equalTypes-ind
          (λ {i} {w} {T1} {T2} eqt → T1 ≡ #ISECT A B → T2 ≡ #ISECT C D → equalTypes i w A C)
          ind eqt


eqTypesNOWRITEMOD→ : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                   → equalTypes i w (#NOWRITEMOD A) (#NOWRITEMOD B)
                   → equalTypes i w A B
eqTypesNOWRITEMOD→ {w} {i} {A} {B} eqtA =
  equalTypesISECT→ₗ {w} {i} {A} {#NOWRITE} {B} {#NOWRITE} eqtA


eqTypesNOREADMOD→ : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                  → equalTypes i w (#NOREADMOD A) (#NOREADMOD B)
                  → equalTypes i w A B
eqTypesNOREADMOD→ {w} {i} {A} {B} eqtA =
  equalTypesISECT→ₗ {w} {i} {A} {#NOREAD} {B} {#NOREAD} eqtA


abstract
  equalTypesSUM!→ₗ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                   → equalTypes i w (#SUM! A B) (#SUM! C D)
                   → equalTypes i w A C
  equalTypesSUM!→ₗ {w} {i} {A} {B} {C} {D} eqt =
    equalTypesSUM→ₗ (eqTypesNOREADMOD→ (eqTypesNOWRITEMOD→ eqt))


abstract
  equalTypesSUM!→ᵣ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                   → equalTypes i w (#SUM! A B) (#SUM! C D)
                   → (a b : CTerm)
                   → equalInType i w A a b
                   → equalTypes i w (sub0 a B) (sub0 b D)
  equalTypesSUM!→ᵣ {w} {i} {A} {B} {C} {D} eqt =
    equalTypesSUM→ᵣ (eqTypesNOREADMOD→ (eqTypesNOWRITEMOD→ eqt))


→equalInType-EQ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                  → equalInType u w A a b
                  → equalInType u w (#EQ a b A) f g
→equalInType-EQ {u} {w} {a} {b} {A} {f} {g} a∈ =
  equalInType-EQ
    (fst a∈)
    (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon a∈ w1 e1))



abstract
  equalInType-UNION!→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm} {f g : CTerm}
                      → equalInType u w (#UNION! A B) f g
                      → □· w (λ w' _ → UNIONeq! (equalInType u w' A) (equalInType u w' B) w' f g)
  equalInType-UNION!→ {u} {w} {A} {B} {f} {g} f∈ =
    Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInTypeNOWRITEMOD→ f∈))
    where
    aw1 : ∀𝕎 w (λ w' e' → NOWRITEMODeq (equalInType u w' (#NOREADMOD (#UNION A B))) w' f g
                        → □· w' (↑wPred' (λ w'' _ → UNIONeq! (equalInType u w'' A)
                                                             (equalInType u w'' B)
                                                             w'' f g) e'))
    aw1 w1 e1 (f∈1 , (c₁ , c₂)) = Mod.□-idem M (Mod.∀𝕎-□Func M aw2 (equalInTypeNOREADMOD→ f∈1))
      where
      aw2 : ∀𝕎 w1 (λ w' e' → NOREADMODeq (equalInType u w' (#UNION A B)) w' f g
                           → □· w' (↑wPred' (↑wPred' (λ w'' _ → UNIONeq! (equalInType u w'' A)
                                                                         (equalInType u w'' B)
                                                                         w'' f g) e1) e'))
      aw2 w2 e2 (f∈2 , (d₁ , d₂)) = Mod.∀𝕎-□Func M aw3 (equalInType-UNION→ f∈2)
        where
        aw3 : ∀𝕎 w2 (λ w' e' → UNIONeq (equalInType u w' A) (equalInType u w' B) w' f g
                             → ↑wPred' (↑wPred' (λ w'' _ → UNIONeq! (equalInType u w'' A)
                                                                    (equalInType u w'' B)
                                                                    w'' f g) e1) e2 w' e')
        aw3 w3 e3 (a₁ , a₂ , inj₁ (i₁ , i₂ , a∈)) z₁ z₂ =
          a₁ , a₂ , inj₁ (noread-nowrite→#⇛! tt (∀𝕎-mon e3 d₁) (∀𝕎-mon (⊑-trans· e2 e3) c₁) i₁ ,
                          noread-nowrite→#⇛! tt (∀𝕎-mon e3 d₂) (∀𝕎-mon (⊑-trans· e2 e3) c₂) i₂ ,
                          a∈)
        aw3 w3 e3 (a₁ , a₂ , inj₂ (i₁ , i₂ , a∈)) z₁ z₂ =
          a₁ , a₂ , inj₂ (noread-nowrite→#⇛! tt (∀𝕎-mon e3 d₁) (∀𝕎-mon (⊑-trans· e2 e3) c₁) i₁ ,
                          noread-nowrite→#⇛! tt (∀𝕎-mon e3 d₂) (∀𝕎-mon (⊑-trans· e2 e3) c₂) i₂ ,
                          a∈)


abstract
  equalInType-UNION! : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                     → isType u w A
                     → isType u w B
                     → □· w (λ w' _ → UNIONeq! (equalInType u w' A) (equalInType u w' B) w' f g)
                     → equalInType u w (#UNION! A B) f g
  equalInType-UNION! {u} {w} {A} {B} {f} {g} ha hb eqi =
    →equalInTypeNOWRITEMOD (Mod.∀𝕎-□Func M aw1 eqi)
    where
    aw1 : ∀𝕎 w (λ w' e' → UNIONeq! (equalInType u w' A) (equalInType u w' B) w' f g
                        → equalInType u w' (#NOREADMOD (#UNION A B)) f g × NOWRITEeq w' f g)
    aw1 w1 e1 (a₁ , a₂ , inj₁ (c₁ , c₂ , a∈)) =
      →equalInTypeNOREADMOD (Mod.∀𝕎-□ M aw2) ,
      #⇛!-pres-#⇓→#⇓!-rev c₁ (#⇓→#⇓!-val w1 (#INL a₁) tt) ,
      #⇛!-pres-#⇓→#⇓!-rev c₂ (#⇓→#⇓!-val w1 (#INL a₂) tt)
        where
        aw2 : ∀𝕎 w1 (λ w' _ → equalInType u w' (#UNION A B) f g × NOREADeq w' f g)
        aw2 w2 e2 =
          →equalInType-UNION
            (eqTypes-mon (uni u) ha w2 (⊑-trans· e1 e2))
            (eqTypes-mon (uni u) hb w2 (⊑-trans· e1 e2))
            (Mod.∀𝕎-□ M aw3) ,
          #⇛val→#⇓→#⇛ {w2} {f} {#INL a₁} tt (#⇛!→#⇛ (∀𝕎-mon e2 c₁)) ,
          #⇛val→#⇓→#⇛ {w2} {g} {#INL a₂} tt (#⇛!→#⇛ (∀𝕎-mon e2 c₂))
            where
            aw3 : ∀𝕎 w2 (λ w' _ → UNIONeq (equalInType u w' A) (equalInType u w' B) w' f g)
            aw3 w3 e3 =
              a₁ , a₂ , inj₁ (#⇓!→#⇓ (lower (c₁ w3 (⊑-trans· e2 e3))) ,
                              #⇓!→#⇓ (lower (c₂ w3 (⊑-trans· e2 e3))) ,
                              equalInType-mon a∈ w3 (⊑-trans· e2 e3))
    aw1 w1 e1 (a₁ , a₂ , inj₂ (c₁ , c₂ , a∈)) =
      →equalInTypeNOREADMOD (Mod.∀𝕎-□ M aw2) ,
      #⇛!-pres-#⇓→#⇓!-rev c₁ (#⇓→#⇓!-val w1 (#INR a₁) tt) ,
      #⇛!-pres-#⇓→#⇓!-rev c₂ (#⇓→#⇓!-val w1 (#INR a₂) tt)
        where
        aw2 : ∀𝕎 w1 (λ w' _ → equalInType u w' (#UNION A B) f g × NOREADeq w' f g)
        aw2 w2 e2 =
          →equalInType-UNION
            (eqTypes-mon (uni u) ha w2 (⊑-trans· e1 e2))
            (eqTypes-mon (uni u) hb w2 (⊑-trans· e1 e2))
            (Mod.∀𝕎-□ M aw3) ,
          #⇛val→#⇓→#⇛ {w2} {f} {#INR a₁} tt (#⇛!→#⇛ (∀𝕎-mon e2 c₁)) ,
          #⇛val→#⇓→#⇛ {w2} {g} {#INR a₂} tt (#⇛!→#⇛ (∀𝕎-mon e2 c₂))
            where
            aw3 : ∀𝕎 w2 (λ w' _ → UNIONeq (equalInType u w' A) (equalInType u w' B) w' f g)
            aw3 w3 e3 =
              a₁ , a₂ , inj₂ (#⇓!→#⇓ (lower (c₁ w3 (⊑-trans· e2 e3))) ,
                              #⇓!→#⇓ (lower (c₂ w3 (⊑-trans· e2 e3))) ,
                              equalInType-mon a∈ w3 (⊑-trans· e2 e3))

\end{code}
