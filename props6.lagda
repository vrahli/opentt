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
open import Axiom.Extensionality.Propositional


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
              (P : Progress {L} W C K)
              (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
              (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (TUNION-eq ; TUNION-eq-base ; TUNION-eq-trans ; TUNION-eq→ ; →TUNION-eq)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (steps→¬Names)
--open import termsPres(W)(C)(K)(G)(X)(N)(EC)
--  using (#¬Enc→⇛! ; #¬Seq→⇛!)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (□·EqTypes→uniUpTo ; uniUpTo→□·EqTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqInType-extr1 ; eqInType-sym ; eqInType-extl1 ; equalInType-sym)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-#⇛-left-rev ; TUNIONeq-#⇛-rev)

--open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
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
¬Names→names[] {DUM a} nn = ¬Names→names[] {a} nn
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

\end{code}
