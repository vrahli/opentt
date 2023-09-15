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
--open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning
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
open import encode


module continuity7 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G)
                   (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                   (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (≡LET ; ≡SUBSING)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (¬Names→steps ; lowerVars++ ; lowerVars-fvars-shiftUp ; lowerVars⊆lowerVars)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (∀𝕎-□Func2 ; ∀𝕎-□Func4)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-#⇛-left-right-rev ; equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev ; equalTerms-pres-#⇛-left-rev-SUM ;
         equalTypes→equalInType ; →equalInTypeSUBSING ; equalInType-#⇛-LR)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-#⇛ₚ-left-right-rev)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)



cont : Term
cont =
  PI (TPURE BAIRE→NAT) -- F
     (PI (TPURE BAIRE) -- f
         (SUBSING (contBody (VAR 3) (VAR 2))))


#cont : CTerm
#cont = ct cont c
  where
    c : # cont
    c = refl



#[0]BAIRE→NAT : CTerm0
#[0]BAIRE→NAT = ct0 BAIRE→NAT c
  where
    c : #[ [ 0 ] ] BAIRE→NAT
    c = refl




--fvars-contBody : (a b : Term) → fvars (contBody a b) ≡ fvars a ++ fvars a
--fvars-contBody a b = ≡++ {_} {_} {fvars a} {fvars a} {fvars b} {fvars b} {!!} {!!}


{--
--}


lowerVars-fvars-shiftUp1 : (t : Term) → lowerVars (fvars (shiftUp 1 t)) ≡ Data.List.map (sucIf≤ 0) (lowerVars (fvars t))
lowerVars-fvars-shiftUp1 t rewrite fvars-shiftUp≡ 1 t | lowerVars-map-sucIf≤-suc 0 (fvars t) = refl


12⊆01234 : 1 ∷ [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
12⊆01234 {x} (here px) rewrite px = there (here refl)
12⊆01234 {x} (there (here px)) rewrite px = there (there (here refl))


12⊆0123 : 1 ∷ [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
12⊆0123 {x} (here px) rewrite px = there (here refl)
12⊆0123 {x} (there (here px)) rewrite px = there (there (here refl))


1234⊆01234 : 1 ∷ 2 ∷ 3 ∷ [ 4 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
1234⊆01234 {x} i = there i

234⊆01234 : 2 ∷ 3 ∷ [ 4 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
234⊆01234 {x} i = there (there i)


123⊆0123 : 1 ∷ 2 ∷ [ 3 ] ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
123⊆0123 {x} i = there i


23⊆012345 : 2 ∷ [ 3 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
23⊆012345 {x} (here px) rewrite px = there (there (here refl))
23⊆012345 {x} (there (here px)) rewrite px = there (there (there (here refl)))


2345⊆012345 : 2 ∷ 3 ∷ 4 ∷ [ 5 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
2345⊆012345 {x} i = there (there i)


2⊆012345 : [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
2⊆012345 {x} (here px) rewrite px = there (there (here refl))


2⊆01234 : [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
2⊆01234 {x} (here px) rewrite px = there (there (here refl))



fvars-shiftUp0-CTerm1 : (a : CTerm1) → fvars (shiftUp 0 ⌜ a ⌝) ⊆ 1 ∷ [ 2 ]
fvars-shiftUp0-CTerm1 a {x} i rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ suc i
... | (z , j , e) rewrite e = q p
  where
    p : z ∈ 0 ∷ [ 1 ]
    p = ⊆?→⊆ (CTerm1.closed a) j

    q : z ∈ 0 ∷ [ 1 ] → suc z ∈ 1 ∷ 2 ∷ []
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)



fvars-shiftUp0-CTerm2 : (a : CTerm2) → fvars (shiftUp 0 ⌜ a ⌝) ⊆ 1 ∷ 2 ∷ [ 3 ]
fvars-shiftUp0-CTerm2 a {x} i rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ suc i
... | (z , j , e) rewrite e = q p
  where
    p : z ∈ 0 ∷ 1 ∷ [ 2 ]
    p = ⊆?→⊆ (CTerm2.closed a) j

    q : z ∈ 0 ∷ 1 ∷ [ 2 ] → suc z ∈ 1 ∷ 2 ∷ [ 3 ]
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)
    q (there (there (here px))) rewrite px = there (there (here refl))



fvars-shiftUp0-CTerm3 : (a : CTerm3) → fvars (shiftUp 0 ⌜ a ⌝) ⊆ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
fvars-shiftUp0-CTerm3 a {x} i rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ suc i
... | (z , j , e) rewrite e = q p
  where
    p : z ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
    p = ⊆?→⊆ (CTerm3.closed a) j

    q : z ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ] → suc z ∈ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)
    q (there (there (here px))) rewrite px = there (there (here refl))
    q (there (there (there (here px)))) rewrite px = there (there (there (here refl)))



fvars-shiftUp10-CTerm : (a : CTerm) → fvars (shiftUp 1 (shiftUp 0 ⌜ a ⌝)) ⊆ []
fvars-shiftUp10-CTerm a {x} i rewrite #shiftUp 0 a | #shiftUp 1 a | CTerm.closed a = i



fvars-shiftUp10-CTerm1 : (a : CTerm1) → fvars (shiftUp 1 (shiftUp 0 ⌜ a ⌝)) ⊆ 2 ∷ [ 3 ]
fvars-shiftUp10-CTerm1 a {x} i rewrite fvars-shiftUp≡ 1 (shiftUp 0 ⌜ a ⌝) with ∈-map⁻ (sucIf≤ 1) i
... | (z , j , e) rewrite e | fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ (sucIf≤ 0) j
... | (z' , j' , e') rewrite e' = q p
  where
    p : z' ∈ 0 ∷ [ 1 ]
    p = ⊆?→⊆ (CTerm1.closed a) j'

    q : z' ∈ 0 ∷ [ 1 ] → suc (suc z') ∈ 2 ∷ 3 ∷ []
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)



fvars-shiftUp10-CTerm2 : (a : CTerm2) → fvars (shiftUp 1 (shiftUp 0 ⌜ a ⌝)) ⊆ 2 ∷ 3 ∷ [ 4 ]
fvars-shiftUp10-CTerm2 a {x} i rewrite fvars-shiftUp≡ 1 (shiftUp 0 ⌜ a ⌝) with ∈-map⁻ (sucIf≤ 1) i
... | (z , j , e) rewrite e | fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ (sucIf≤ 0) j
... | (z' , j' , e') rewrite e' = q p
  where
    p : z' ∈ 0 ∷ 1 ∷ [ 2 ]
    p = ⊆?→⊆ (CTerm2.closed a) j'

    q : z' ∈ 0 ∷ 1 ∷ [ 2 ] → suc (suc z') ∈ 2 ∷ 3 ∷ [ 4 ]
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)
    q (there (there (here px))) rewrite px = there (there (here refl))



fvars-shiftUp10-CTerm3 : (a : CTerm3) → fvars (shiftUp 1 (shiftUp 0 ⌜ a ⌝)) ⊆ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
fvars-shiftUp10-CTerm3 a {x} i rewrite fvars-shiftUp≡ 1 (shiftUp 0 ⌜ a ⌝) with ∈-map⁻ (sucIf≤ 1) i
... | (z , j , e) rewrite e | fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ (sucIf≤ 0) j
... | (z' , j' , e') rewrite e' = q p
  where
    p : z' ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
    p = ⊆?→⊆ (CTerm3.closed a) j'

    q : z' ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ] → suc (suc z') ∈ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)
    q (there (there (here px))) rewrite px = there (there (here refl))
    q (there (there (there (here px)))) rewrite px = there (there (there (here refl)))



2⊆0123 : [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
2⊆0123 {x} (here px) rewrite px = there (there (here refl))


2⊆012 : [ 2 ] ⊆ 0 ∷ 1 ∷ [ 2 ]
2⊆012 {x} (here px) rewrite px = there (there (here refl))


3⊆0123 : [ 3 ] ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
3⊆0123 {x} (here px) rewrite px = there (there (there (here refl)))


lowerVars2-map-sucIf≤1 : (l : List Var)
                       → lowerVars (lowerVars (Data.List.map (sucIf≤ 1) (Data.List.map suc l)))
                       ≡ l
lowerVars2-map-sucIf≤1 [] = refl
lowerVars2-map-sucIf≤1 (x ∷ l)
  rewrite lowerVars2-map-sucIf≤1 l
  = refl


lowerVars2-fvars-shiftUp1 : (b : Term)
                          → lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))
                          ≡ fvars b
lowerVars2-fvars-shiftUp1 b
  rewrite fvars-shiftUp≡ 1 (shiftUp 0 b) | fvars-shiftUp≡ 0 b
  = lowerVars2-map-sucIf≤1 (fvars b)


-- a couple of lowerVars because of SUM and PI?
fvars-contBody : (a b : Term)
               → fvars (contBody a b) ⊆ lowerVars (lowerVars (fvars a)) ++ lowerVars (lowerVars (fvars b))
fvars-contBody a b {x} i
  rewrite sucIf≤00
        | lowerVars++ (fvars (shiftUp 1 (shiftUp 0 a)) ++ fvars (shiftUp 1 (shiftUp 0 b)))
                      ((fvars (shiftUp 1 (shiftUp 0 a)) ++ 2 ∷ []) ++ [])
        | ++[] (fvars (shiftUp 1 (shiftUp 0 a)) ++ 2 ∷ [])
        | lowerVars++ (fvars (shiftUp 1 (shiftUp 0 a))) (fvars (shiftUp 1 (shiftUp 0 b)))
        | lowerVars++ (fvars (shiftUp 1 (shiftUp 0 a))) (2 ∷ [])
        | lowerVars++ (fvars (shiftUp 0 b) ++ 1 ∷ 2 ∷ [])
                      ((lowerVars (fvars (shiftUp 1 (shiftUp 0 a))) ++ lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))
                       ++ lowerVars (fvars (shiftUp 1 (shiftUp 0 a))) ++ 1 ∷ [])
        | lowerVars++ (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))) ++ lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))
                      (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))) ++ 1 ∷ [])
        | lowerVars++ (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))) (1 ∷ [])
        | lowerVars++ (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))) (lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))
        | lowerVars++ (fvars (shiftUp 0 b)) (1 ∷ 2 ∷ [])
        | lowerVars++ (lowerVars (fvars (shiftUp 0 b)) ++ 0 ∷ 1 ∷ [])
                      ((lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))) ++ lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b)))))
                       ++ lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))) ++ 0 ∷ [])
        | lowerVars++ (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))) ++ lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b)))))
                      (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))) ++ 0 ∷ [])
        | lowerVars++ (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))))) (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b)))))
        | lowerVars++ (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))))) (0 ∷ [])
        | lowerVars++ (lowerVars (fvars (shiftUp 0 b))) (0 ∷ 1 ∷ [])
        | lowerVars++ (lowerVars (lowerVars (fvars (shiftUp 0 b))) ++ 0 ∷ [])
                      ((lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))))
                        ++ lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))))
                       ++ lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))))
                       ++ [])
        | lowerVars++ (lowerVars (lowerVars (fvars (shiftUp 0 b)))) (0 ∷ [])
        | lowerVars++ (lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a)))))
                       ++ lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))))
                      (lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))))) ++ [])
        | ++[] (lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))))))
        | ++[] (lowerVars (lowerVars (lowerVars (fvars (shiftUp 0 b)))))
        | lowerVars++ (lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 a))))))
                      (lowerVars (lowerVars (lowerVars (fvars (shiftUp 1 (shiftUp 0 b))))))
        | lowerVars-fvars-shiftUp b
        | lowerVars2-fvars-shiftUp1 a
        | lowerVars2-fvars-shiftUp1 b
  with ∈-++⁻ (lowerVars (lowerVars (fvars b))) i
... | inj₁ p = ∈-++⁺ʳ (lowerVars (lowerVars (fvars a))) p
... | inj₂ p with ∈-++⁻ (lowerVars (lowerVars (fvars a)) ++ lowerVars (lowerVars (fvars b))) p
... | inj₁ q = q
... | inj₂ q = ∈-++⁺ˡ q


lowerVars2-fvars-CTerm2⊆ : (a : CTerm2)
                         → lowerVars (lowerVars (fvars ⌜ a ⌝)) ⊆ [ 0 ]
lowerVars2-fvars-CTerm2⊆ a =
  lowerVars⊆lowerVars
    (lowerVars (fvars ⌜ a ⌝))
    (lowerVars (0 ∷ 1 ∷ [ 2 ]))
    (lowerVars⊆lowerVars (fvars ⌜ a ⌝) (0 ∷ 1 ∷ [ 2 ]) (⊆?→⊆ (CTerm2.closed a)))


lowerVars2-fvars-CTerm⊆ : (a : CTerm)
                        → lowerVars (lowerVars (fvars ⌜ a ⌝)) ⊆ []
lowerVars2-fvars-CTerm⊆ a =
  lowerVars⊆lowerVars
    (lowerVars (fvars ⌜ a ⌝))
    (lowerVars [])
    (lowerVars⊆lowerVars (fvars ⌜ a ⌝) [] (≡[]→⊆[] (CTerm.closed a)))


lowerVars2-fvars-CTerm3⊆ : (a : CTerm3)
                         → lowerVars (lowerVars (fvars ⌜ a ⌝)) ⊆ 0 ∷ [ 1 ]
lowerVars2-fvars-CTerm3⊆ a =
  lowerVars⊆lowerVars
    (lowerVars (fvars ⌜ a ⌝))
    (lowerVars (0 ∷ 1 ∷ 2 ∷ [ 3 ]))
    (lowerVars⊆lowerVars (fvars ⌜ a ⌝) (0 ∷ 1 ∷ 2 ∷ [ 3 ]) (⊆?→⊆ (CTerm3.closed a)))


lowerVars2-fvars-CTerm4⊆ : (a : CTerm4)
                         → lowerVars (lowerVars (fvars ⌜ a ⌝)) ⊆ 0 ∷ 1 ∷ [ 2 ]
lowerVars2-fvars-CTerm4⊆ a =
  lowerVars⊆lowerVars
    (lowerVars (fvars ⌜ a ⌝))
    (lowerVars (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]))
    (lowerVars⊆lowerVars (fvars ⌜ a ⌝) (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]) (⊆?→⊆ (CTerm4.closed a)))


lowerVars2-fvars-CTerm5⊆ : (a : CTerm5)
                         → lowerVars (lowerVars (fvars ⌜ a ⌝)) ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
lowerVars2-fvars-CTerm5⊆ a =
  lowerVars⊆lowerVars
    (lowerVars (fvars ⌜ a ⌝))
    (lowerVars (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]))
    (lowerVars⊆lowerVars (fvars ⌜ a ⌝) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]) (⊆?→⊆ (CTerm5.closed a)))


#[0]contBody : CTerm → CTerm2 → CTerm0
#[0]contBody a b = ct0 (contBody ⌜ a ⌝ ⌜ b ⌝) c
  where
  c : #[ [ 0 ] ] contBody ⌜ a ⌝ ⌜ b ⌝
  c = ⊆→⊆? {fvars (contBody ⌜ a ⌝ ⌜ b ⌝)} {[ 0 ]}
             (⊆-trans (fvars-contBody ⌜ a ⌝ ⌜ b ⌝)
                      (++⊆ {_} {_}
                           {lowerVars (lowerVars (fvars ⌜ a ⌝))}
                           {lowerVars (lowerVars (fvars ⌜ b ⌝))}
                           (⊆-trans (lowerVars2-fvars-CTerm⊆ a) (λ ()))
                           (lowerVars2-fvars-CTerm2⊆ b)))


#[1]contBody : CTerm3 → CTerm3 → CTerm1
#[1]contBody a b = ct1 (contBody ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] contBody ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars (contBody ⌜ a ⌝ ⌜ b ⌝)} {0 ∷ [ 1 ]}
             (⊆-trans (fvars-contBody ⌜ a ⌝ ⌜ b ⌝)
                      (++⊆ {_} {_}
                           {lowerVars (lowerVars (fvars ⌜ a ⌝))}
                           {lowerVars (lowerVars (fvars ⌜ b ⌝))}
                           (lowerVars2-fvars-CTerm3⊆ a) (lowerVars2-fvars-CTerm3⊆ b)))


#[2]contBody : CTerm4 → CTerm4 → CTerm2
#[2]contBody a b = ct2 (contBody ⌜ a ⌝ ⌜ b ⌝) c
  where
  c : #[ 0 ∷ 1 ∷ [ 2 ] ] contBody ⌜ a ⌝ ⌜ b ⌝
  c = ⊆→⊆? {fvars (contBody ⌜ a ⌝ ⌜ b ⌝)} {0 ∷ 1 ∷ [ 2 ]}
           (⊆-trans (fvars-contBody ⌜ a ⌝ ⌜ b ⌝)
                      (++⊆ {_} {_}
                           {lowerVars (lowerVars (fvars ⌜ a ⌝))}
                           {lowerVars (lowerVars (fvars ⌜ b ⌝))}
                           (lowerVars2-fvars-CTerm4⊆ a) (lowerVars2-fvars-CTerm4⊆ b)))


#[3]contBody : CTerm5 → CTerm5 → CTerm3
#[3]contBody a b = ct3 (contBody ⌜ a ⌝ ⌜ b ⌝) c
  where
  c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] contBody ⌜ a ⌝ ⌜ b ⌝
  c = ⊆→⊆? {fvars (contBody ⌜ a ⌝ ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
           (⊆-trans (fvars-contBody ⌜ a ⌝ ⌜ b ⌝)
                      (++⊆ {_} {_}
                           {lowerVars (lowerVars (fvars ⌜ a ⌝))}
                           {lowerVars (lowerVars (fvars ⌜ b ⌝))}
                           (lowerVars2-fvars-CTerm5⊆ a) (lowerVars2-fvars-CTerm5⊆ b)))


-- MOVE
#[2]SUBSING : CTerm2 → CTerm2
#[2]SUBSING t = ct2 (SUBSING ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SUBSING ⌜ t ⌝
    c = CTerm2.closed t


-- MOVE
#[3]SUBSING : CTerm3 → CTerm3
#[3]SUBSING t = ct3 (SUBSING ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] SUBSING ⌜ t ⌝
    c = CTerm3.closed t


#CONT : CTerm
#CONT =
  #PI (#TPURE #BAIRE→NAT)
      (#[0]PI (#[0]TPURE #[0]BAIRE)
              (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))



contExt : Term
--contExt = LAMBDA (LAMBDA (PAIR (νtestM (VAR 1) (VAR 0)) lam3AX))
contExt = LAMBDA (LAMBDA (LET (VAR 1) (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))))



#contExt : CTerm
#contExt = ct contExt c
  where
    c : # contExt
    c = refl


#cont≡ : #cont ≡ #CONT
#cont≡ = refl


isType-BAIRE→NAT : (i : ℕ) (w : 𝕎·) → isType i w #BAIRE→NAT
isType-BAIRE→NAT i w =
  ≡CTerm→eqTypes (sym #BAIRE→NAT≡) (sym #BAIRE→NAT≡) (eqTypesFUN← eqTypesBAIRE eqTypesNAT)


sub0-cont-b1 : (F : CTerm)
               → sub0 F (#[0]PI (#[0]TPURE #[0]BAIRE) (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))
               ≡ #PI (#TPURE #BAIRE) (#[0]SUBSING (#[0]contBody F #[2]VAR2))
sub0-cont-b1 F = CTerm≡ e0
  where
    e0 : sub ⌜ F ⌝ (PI (TPURE BAIRE)
                      (SUBSING (contBody (VAR 3) (VAR 2))))
         ≡ PI (TPURE BAIRE)
              (SUBSING (contBody ⌜ F ⌝ (VAR 2)))
    e0 rewrite #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F
             | #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F
             | #shiftDown 0 F | #shiftDown 7 F
             | #shiftUp 1 F | #shiftUp 4 F | #shiftDown 5 F = refl --refl


sub0-cont-b2 : (F f : CTerm)
               → sub0 f (#[0]SUBSING (#[0]contBody F #[2]VAR2))
                  ≡ #SUBSING (#contBody F f)
sub0-cont-b2 F f = CTerm≡ e0
  where
    e0 : sub ⌜ f ⌝ (SUBSING (contBody ⌜ F ⌝ (VAR 2)))
         ≡ SUBSING (contBody ⌜ F ⌝ ⌜ f ⌝)
    e0 rewrite #shiftUp 0 F | #shiftUp 4 F | #shiftUp 6 F | #shiftUp 1 F | #shiftUp 4 F
             | #shiftUp 0 f | #shiftUp 0 f | #shiftUp 0 f | #shiftUp 0 f | #shiftUp 0 f | #shiftUp 0 f
             | #shiftUp 3 f | #shiftDown 4 f | #shiftUp 1 f
             | subv# 4 ⌜ f  ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #shiftDown 4 f | #shiftDown 4 F | #shiftDown 3 f = refl


sub0-cont-b3 : (F : CTerm)
             → sub0 F (#[0]PI (#[0]TPURE #[0]BAIRE)
                              (#[1]LET #[1]VAR1
                                       (#[2]LET #[2]VAR1
                                                (#[3]SUBSING (#[3]contBody #[5]VAR3 #[5]VAR2)))))
             ≡ #PI (#TPURE #BAIRE)
                   (#[0]LET ⌞ F ⌟
                            (#[1]LET #[1]VAR1
                                     (#[2]SUBSING (#[2]contBody #[4]VAR3 #[4]VAR2))))
sub0-cont-b3 F = CTerm≡ (≡PI refl (→≡LET e0 refl))
  where
  e0 : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ F ⌝)) ≡ ⌜ CTerm→CTerm0 F ⌝
  e0 rewrite #shiftUp 0 F | #shiftUp 0 F | CTerm→CTerm0→Term F | #shiftDown 1 F = refl


sub0-cont-b4 : (F f : CTerm)
             → sub0 f (#[0]LET ⌞ F ⌟ (#[1]LET #[1]VAR1 (#[2]SUBSING (#[2]contBody #[4]VAR3 #[4]VAR2))))
             ≡ #LET F (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))
sub0-cont-b4 F f = CTerm≡ (→≡LET e0 (→≡LET e1 refl))
  where
  e0 : shiftDown 0 (subv 0 (shiftUp 0 ⌜ f ⌝) ⌜ CTerm→CTerm0 F ⌝) ≡ ⌜ F ⌝
  e0 rewrite CTerm→CTerm0→Term F | subv# 0 (shiftUp 0 ⌜ f ⌝) ⌜ F ⌝ (CTerm.closed F) | #shiftDown 0 F = refl

  e1 : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ f ⌝)) ≡ ⌜ CTerm→CTerm0 f ⌝
  e1 rewrite #shiftUp 0 f | #shiftUp 0 f | CTerm→CTerm0→Term f | #shiftDown 1 f = refl


cont-LET-#⇛!₂ : (w : 𝕎·) (F f : CTerm)
              → #isValue F
              → #LET F (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))
                 #⇛! #LET f (#[0]SUBSING (#[0]contBody F #[2]VAR2)) at w
cont-LET-#⇛!₂ w F f isv w1 e1 =
  lift (1 , c)
  where
  c : steps 1 (⌜ #LET F (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))) ⌝ , w1)
    ≡ (⌜ #LET f (#[0]SUBSING (#[0]contBody F #[2]VAR2)) ⌝ , w1)
  c with isValue⊎ ⌜ F ⌝
  ... | inj₁ p
    rewrite #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F
          | #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F
          | #shiftDown 5 F | #shiftUp 1 F
          | subv# 0 ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed f) | #shiftDown 0 f
    = refl
  ... | inj₂ p = ⊥-elim (p isv)


cont-LET-#⇛!₃ : (w : 𝕎·) (G g : CTerm)
              → #isValue g
              → #LET g (#[0]SUBSING (#[0]contBody G #[2]VAR2)) #⇛! #SUBSING (#contBody G g) at w
cont-LET-#⇛!₃ w G g isv w1 e1 =
  lift (1 , c)
  where
  c : steps 1 (⌜ #LET g (#[0]SUBSING (#[0]contBody G #[2]VAR2)) ⌝ , w1) ≡ (⌜ #SUBSING (#contBody G g) ⌝ , w1)
  c with isValue⊎ ⌜ g ⌝
  ... | inj₁ p
    rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 g
          | #shiftDown 0 g | #shiftDown 4 g | #shiftDown 3 g | #shiftUp 1 g
          | #shiftUp 0 G | #shiftUp 1 G
          | subv# 4 ⌜ g ⌝ ⌜ G ⌝ (CTerm.closed G)
          | #shiftDown 4 G
    = refl
  ... | inj₂ p = ⊥-elim (p isv)


cont-LET-#⇛!₄ : (w : 𝕎·) (F G f g : CTerm)
              → #isValue G
              → #isValue g
              → F #⇛! G at w
              → f #⇛! g at w
              → #LET F (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))
                 #⇛! #SUBSING (#contBody G g) at w
cont-LET-#⇛!₄ w F G f g isvG isvg cG cg =
  #⇛!-trans {w}
    {#LET F (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
    {#LET G (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
    {#SUBSING (#contBody G g)}
    (LET-#⇛! w F G (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))) cG)
    (#⇛!-trans {w}
       {#LET G (#[0]LET ⌞ f ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
       {#LET f (#[0]SUBSING (#[0]contBody G #[2]VAR2))}
       {#SUBSING (#contBody G g)}
       (cont-LET-#⇛!₂ w G f isvG)
       (#⇛!-trans {w}
          {#LET f (#[0]SUBSING (#[0]contBody G #[2]VAR2))}
          {#LET g (#[0]SUBSING (#[0]contBody G #[2]VAR2))}
          {#SUBSING (#contBody G g)}
          (LET-#⇛! w f g (#[0]SUBSING (#[0]contBody G #[2]VAR2)) cg)
          (cont-LET-#⇛!₃ w G g isvg)))


equalTypes-cont-PI0 : (i : ℕ) (w : 𝕎·) (F₁ F₂ : CTerm)
                    → equalInType i w (#TPURE #BAIRE→NAT) F₁ F₂
                    → equalTypes i w (#PI (#TPURE #BAIRE)
                                          (#[0]LET ⌞ F₁ ⌟ (#[1]LET #[1]VAR1 (#[2]SUBSING (#[2]contBody #[4]VAR3 #[4]VAR2)))))
                                     (#PI (#TPURE #BAIRE)
                                          (#[0]LET ⌞ F₂ ⌟ (#[1]LET #[1]VAR1 (#[2]SUBSING (#[2]contBody #[4]VAR3 #[4]VAR2)))))
equalTypes-cont-PI0 i w F₁ F₂ eF =
  eqTypesPI← (λ w' e' → equalTypesTPURE eqTypesBAIRE)
    h2
  where
  h2 : ∀𝕎 w (λ w1 e2 → (a₁ a₂ : CTerm)
                     → equalInType i w1 (#TPURE #BAIRE) a₁ a₂
                     → equalTypes
                         i w1
                         (sub0 a₁ (#[0]LET ⌞ F₁ ⌟ (#[1]LET #[1]VAR1 (#[2]SUBSING (#[2]contBody #[4]VAR3 #[4]VAR2)))))
                         (sub0 a₂ (#[0]LET ⌞ F₂ ⌟ (#[1]LET #[1]VAR1 (#[2]SUBSING (#[2]contBody #[4]VAR3 #[4]VAR2))))))
  h2 w1 e1 f₁ f₂ ef =
    ≡CTerm→eqTypes
      (sym (sub0-cont-b4 F₁ f₁))
      (sym (sub0-cont-b4 F₂ f₂))
      h3
    where
    h3 : equalTypes i w1
         (#LET F₁ (#[0]LET ⌞ f₁ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))))
         (#LET F₂ (#[0]LET ⌞ f₂ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))))
    h3 =
      eqTypes-local
        (∀𝕎-□Func4
          aw1
          (equalInType-TPURE-BAIREₗ i w1 f₁ f₂ ef)
          (equalInType-TPURE-BAIREᵣ i w1 f₁ f₂ ef)
          (equalInType-TPURE-BAIRE→NATₗ i w1 F₁ F₂ (equalInType-mon eF w1 e1))
          (equalInType-TPURE-BAIRE→NATᵣ i w1 F₁ F₂ (equalInType-mon eF w1 e1))) -- We need to compute F₁ & F₂
      where
      aw1 : ∀𝕎 w1 (λ w' e' → #⇛!nv f₁ w'
                           → #⇛!nv f₂ w'
                           → #⇛!nv F₁ w'
                           → #⇛!nv F₂ w'
                           → equalTypes i w' (#LET F₁ (#[0]LET ⌞ f₁ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))))
                                             (#LET F₂ (#[0]LET ⌞ f₂ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))))
      aw1 w2 e2 (g₁ , c₁ , n₁ , x₁ , i₁) (g₂ , c₂ , n₂ , x₂ , i₂) (G₁ , d₁ , m₁ , y₁ , j₁) (G₂ , d₂ , m₂ , y₂ , j₂) =
        equalTypes-#⇛-left-right-rev
          {i} {w2}
          {#SUBSING (#contBody G₁ g₁)}
          {#LET F₁ (#[0]LET ⌞ f₁ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
          {#LET F₂ (#[0]LET ⌞ f₂ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
          {#SUBSING (#contBody G₂ g₂)}
          (#⇛!→#⇛ {w2}
            {#LET F₁ (#[0]LET ⌞ f₁ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
            {#SUBSING (#contBody G₁ g₁)}
            (cont-LET-#⇛!₄ w2 F₁ G₁ f₁ g₁ j₁ i₁ d₁ c₁))
          (#⇛!→#⇛ {w2}
            {#LET F₂ (#[0]LET ⌞ f₂ ⌟ (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))}
            {#SUBSING (#contBody G₂ g₂)}
            (cont-LET-#⇛!₄ w2 F₂ G₂ f₂ g₂ j₂ i₂ d₂ c₂))
          (eqTypesSUBSING←
            (equalTypes-contBody i w2 G₁ G₂ g₁ g₂
              (equalInType-#⇛-LR {i} {w2} {#BAIRE→NAT} {F₁} {G₁} {F₂} {G₂} d₁ d₂ (equalInType-mon (equalInType-TPURE→ eF) w2 (⊑-trans· e1 e2)))
              (equalInType-#⇛-LR {i} {w2} {#BAIRE} {f₁} {g₁} {f₂} {g₂} c₁ c₂ (equalInType-mon (equalInType-TPURE→ ef) w2 e2))))


equalTypes-cont-PI : (i : ℕ) (w : 𝕎·) (F₁ F₂ : CTerm)
                     → equalInType i w (#TPURE #BAIRE→NAT) F₁ F₂
                     → equalTypes i w (#PI (#TPURE #BAIRE) (#[0]SUBSING (#[0]contBody F₁ #[2]VAR2)))
                                      (#PI (#TPURE #BAIRE) (#[0]SUBSING (#[0]contBody F₂ #[2]VAR2)))
equalTypes-cont-PI i w F₁ F₂ eF =
  eqTypesPI← (λ w' e' → equalTypesTPURE eqTypesBAIRE) h2
  where
    h2 : ∀𝕎 w (λ w1 e2 → (a₁ a₂ : CTerm)
                         → equalInType i w1 (#TPURE #BAIRE) a₁ a₂
                         → equalTypes
                             i w1
                             (sub0 a₁ (#[0]SUBSING (#[0]contBody F₁ #[2]VAR2)))
                             (sub0 a₂ (#[0]SUBSING (#[0]contBody F₂ #[2]VAR2))))
    h2 w2 e2 f₁ f₂ ef =
      ≡CTerm→eqTypes
        (sym (sub0-cont-b2 F₁ f₁))
        (sym (sub0-cont-b2 F₂ f₂))
        (eqTypesSUBSING←
          (equalTypes-contBody
            i w2 F₁ F₂ f₁ f₂
            (equalInType-mon (equalInType-TPURE→ eF) w2 e2)
            (equalInType-TPURE→ ef)))


sub-lam-pair-test1 : (F : Term) (cF : # F) (nnF : ¬Names F)
                     → LAMBDA (PAIR (νtestM F (VAR 2)) lam3AX)
                     ≡ sub F (LAMBDA (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))
sub-lam-pair-test1 F cF nnF
  rewrite cF | #shiftUp 0 (ct F cF) | #shiftUp 0 (ct F cF)
        | ¬Names→shiftNameUp≡ F 0 nnF
        | #shiftUp 0 (ct F cF) | #shiftDown 2 (ct F cF) = refl


sub-lam-pair-test2 : (F f : Term) (cF : # F) (cf : # f) (nnf : ¬Names f)
                     → PAIR (νtestM F f) lam3AX
                     ≡ sub f (PAIR (νtestM F (VAR 2)) lam3AX)
sub-lam-pair-test2 F f cF cf nnf
  rewrite cf | #shiftUp 0 (ct F cF) | #shiftUp 0 (ct f cf) | #shiftUp 3 (ct f cf)
        | subv# 1 (shiftUp 0 (shiftNameUp 0 f)) F cF | #shiftDown 1 (ct F cF)
        | ¬Names→shiftNameUp≡ f 0 nnf
        | #shiftUp 0 (ct f cf) | #shiftUp 0 (ct f cf) | #shiftUp 0 (ct f cf) | #shiftUp 0 (ct f cf)
        | #shiftDown 4 (ct f cf) = refl


sub-lam-pair-test3 : (F : Term) (#F : # F)
                   → LAMBDA (LET F (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)))
                   ≡ sub F (LAMBDA (LET (VAR 1) (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))))
sub-lam-pair-test3 F #F
  rewrite #F | #shiftUp 0 (ct F #F) | #shiftUp 0 (ct F #F) | #shiftDown 1 (ct F #F)
  = refl


sub-lam-pair-test4 : (F f : Term) (#F : # F) (#f : # f)
                   → LET F (LET f (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))
                   ≡ sub f (LET F (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)))
sub-lam-pair-test4 F f #F #f
  rewrite #F | #shiftUp 0 (ct f #f) | #shiftUp 0 (ct f #f) | #shiftDown 1 (ct f #f)
        | #subv 0 f F #F | #shiftDown 0 (ct F #F)
  = refl


sub-lam-pair-test5 : (F f : Term) (#F : # F) (#f : # f) (nnF : ¬Names F)
                   → LET f (PAIR (νtestM F (VAR 2)) lam3AX)
                   ≡ sub F (LET f (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))
sub-lam-pair-test5 F f #F #f nnF
  rewrite #F | #shiftUp 0 (ct F #F) | #shiftUp 0 (ct F #F)
        | ¬Names→shiftNameUp≡ F 0 nnF
        | #shiftDown 2 (ct F #F)
        | #subv 0 f F #F | #shiftDown 0 (ct F #F)
        | #shiftUp 0 (ct F #F) | #shiftDown 2 (ct F #F)
        | #subv 0 F f #f | #shiftDown 0 (ct f #f)
  = refl


-- TODO: both F and f are reduced now
APP-contExt⇛ : (w : 𝕎·) (F G f g : CTerm)
             → #¬Names G
             → #¬Names g
             → #isValue G
             → #isValue g
             → F #⇛! G at w
             → f #⇛! g at w
             → #APPLY (#APPLY #contExt F) f #⇛! #PAIR (#νtestM G g) #lam3AX at w
APP-contExt⇛ w F G f g nnG nng isvG isvg cF cf =
  ⇛!-trans {w}
    {APPLY (APPLY contExt ⌜ F ⌝) ⌜ f ⌝}
    {APPLY (LAMBDA (LET ⌜ F ⌝ (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)))) ⌜ f ⌝}
    {PAIR (νtestM ⌜ G ⌝ ⌜ g ⌝) lam3AX}
    (→-⇛!-APPLY ⌜ f ⌝
      (≡→APPLY-LAMBDA⇛! w
         (LAMBDA (LET (VAR 1) (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))))
         ⌜ F ⌝
         (LAMBDA (LET ⌜ F ⌝ (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))))
         (sub-lam-pair-test3 ⌜ F ⌝ (CTerm.closed F))))
    (⇛!-trans {w}
       {APPLY (LAMBDA (LET ⌜ F ⌝ (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)))) ⌜ f ⌝}
       {LET ⌜ F ⌝ (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))}
       {PAIR (νtestM ⌜ G ⌝ ⌜ g ⌝) lam3AX}
       (≡→APPLY-LAMBDA⇛! w
          (LET ⌜ F ⌝ (LET (VAR 1) (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)))
          ⌜ f ⌝
          (LET ⌜ F ⌝ (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)))
          (sub-lam-pair-test4 ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)))
       (⇛!-trans {w}
          {LET ⌜ F ⌝ (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))}
          {LET ⌜ G ⌝ (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))}
          {PAIR (νtestM ⌜ G ⌝ ⌜ g ⌝) lam3AX}
          (→-⇛!-LET (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX)) cF)
          (⇛!-trans {w}
             {LET ⌜ G ⌝ (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))}
             {LET ⌜ f ⌝ (PAIR (νtestM ⌜ G ⌝ (VAR 2)) lam3AX)}
             {PAIR (νtestM ⌜ G ⌝ ⌜ g ⌝) lam3AX}
             (≡→LET-VAL⇛! w
                (LET ⌜ f ⌝ (PAIR (νtestM (VAR 1) (VAR 2)) lam3AX))
                ⌜ G ⌝
                (LET ⌜ f ⌝ (PAIR (νtestM ⌜ G ⌝ (VAR 2)) lam3AX))
                isvG
                (sub-lam-pair-test5 ⌜ G ⌝ ⌜ f ⌝ (CTerm.closed G) (CTerm.closed f) nnG))
             (⇛!-trans {w} {LET ⌜ f ⌝ (PAIR (νtestM ⌜ G ⌝ (VAR 2)) lam3AX)}
                {LET ⌜ g ⌝ (PAIR (νtestM ⌜ G ⌝ (VAR 2)) lam3AX)}
                {PAIR (νtestM ⌜ G ⌝ ⌜ g ⌝) lam3AX}
                (→-⇛!-LET (PAIR (νtestM ⌜ G ⌝ (VAR 2)) lam3AX) cf)
                (≡→LET-VAL⇛! w
                   (PAIR (νtestM ⌜ G ⌝ (VAR 2)) lam3AX)
                   ⌜ g ⌝
                   (PAIR (νtestM ⌜ G ⌝ ⌜ g ⌝) lam3AX)
                   isvg
                   (sub-lam-pair-test2 ⌜ G ⌝ ⌜ g ⌝ (CTerm.closed G) (CTerm.closed g) nng))))))


continuityBody-aux2 : (cn : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
                      (i : ℕ) (w : 𝕎·) (F G f g : CTerm)
                    → #¬Names G
                    → #¬Names g
                    → #isValue G
                    → #isValue g
                    → F #⇛! G at w
                    → f #⇛! g at w
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → ∈Type i w (#contBody G g) (#APPLY (#APPLY #contExt F) f)
continuityBody-aux2 cn exb gc i w F G f g nnG nng isvG isvg cF cf eF ef =
  equalInType-#⇛ₚ-left-right-rev
    (APP-contExt⇛ w F G f g nnG nng isvG isvg cF cf)
    (APP-contExt⇛ w F G f g nnG nng isvG isvg cF cf)
    (continuityBody cn exb gc i w G g nnG nng {--nnF nnf--} (#⇛!→∈Type eF cF) (#⇛!→∈Type ef cf) {--eF ef--})


#⇛!→equalTypes-contBody : {i : ℕ} {w : 𝕎·} {F G f g : CTerm}
                        → ∈Type i w #BAIRE→NAT F
                        → ∈Type i w #BAIRE f
                        → F #⇛! G at w
                        → f #⇛! g at w
                        → equalTypes i w (#contBody F f) (#contBody G g)
#⇛!→equalTypes-contBody {i} {w} {F} {G} {f} {g} F∈ f∈ cF cf =
  equalTypes-contBody i w F G f g
    (#⇛!→equalInTypeᵣ F∈ cF)
    (#⇛!→equalInTypeᵣ f∈ cf)


continuityBody-aux : (cn : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
                     (i : ℕ) (w : 𝕎·) (F f : CTerm)
                   → □· w (λ w' e → #⇛!nv F w') --#¬Names F
                   → □· w (λ w' e → #⇛!nv f w') --#¬Names f
                   → ∈Type i w #BAIRE→NAT F
                   → ∈Type i w #BAIRE f
                   → ∈Type i w (#contBody F f) (#APPLY (#APPLY #contExt F) f)
continuityBody-aux cn exb gc i w F f nnF nnf eF ef =
  equalInType-local (∀𝕎-□Func2 aw nnf nnF)
  where
  aw : ∀𝕎 w (λ w' e' → #⇛!nv f w' → #⇛!nv F w'
                     → ∈Type i w' (#contBody F f) (#APPLY (#APPLY #contExt F) f))
  aw w1 e1 (g₁ , cg , nng , neg , isvg) (G₁ , cG , nnG , neG , isvG) =
    equalTypes→equalInType
      (TEQsym-equalTypes
        i w1 (#contBody F f) (#contBody G₁ g₁)
        (#⇛!→equalTypes-contBody {i} {w1} {F} {G₁} {f} {g₁} (equalInType-mon eF w1 e1) (equalInType-mon ef w1 e1) cG cg))
      (continuityBody-aux2 cn exb gc i w1 F G₁ f g₁ nnG nng isvG isvg cG cg (equalInType-mon eF w1 e1) (equalInType-mon ef w1 e1))


continuity : (cn : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
             (i : ℕ) (w : 𝕎·)
             → ∈Type i w #cont #contExt
continuity cn exb gc i w =
  ≡CTerm→equalInType (sym #cont≡)
    (equalInType-PI {i} {w} {#TPURE #BAIRE→NAT}
       {#[0]PI (#[0]TPURE #[0]BAIRE) (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))}
       (λ w' e' → equalTypesTPURE (isType-BAIRE→NAT i w'))
       h1 aw1)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                        → equalInType i w' (#TPURE #BAIRE→NAT) a₁ a₂
                        → equalInType i w' (sub0 a₁ (#[0]PI (#[0]TPURE #[0]BAIRE)
                                                            (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))))
                                            (#APPLY #contExt a₁) (#APPLY #contExt a₂))
    aw1 w1 e1 F₁ F₂ eF =
      ≡CTerm→equalInType
        (sym (sub0-cont-b1 F₁))
        (equalInType-PI
          (λ w' e' → equalTypesTPURE eqTypesBAIRE)
          (λ w2 e2 f₁ f₂ ef →
              ≡CTerm→eqTypes
                (sym (sub0-cont-b2 F₁ f₁))
                (sym (sub0-cont-b2 F₁ f₂))
                (eqTypesSUBSING←
                  (equalTypes-contBody
                    i w2 F₁ F₁ f₁ f₂
                    (equalInType-mon (equalInType-refl (equalInType-TPURE→ eF)) w2 e2)
                    (equalInType-TPURE→ ef))))
          aw2)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f₁ f₂ : CTerm)
                             → equalInType i w' (#TPURE #BAIRE) f₁ f₂
                             → equalInType i w' (sub0 f₁ (#[0]SUBSING (#[0]contBody F₁ #[2]VAR2)))
                                                 (#APPLY (#APPLY #contExt F₁) f₁)
                                                 (#APPLY (#APPLY #contExt F₂) f₂))
        aw2 w2 e2 f₁ f₂ ef =
          ≡CTerm→equalInType
            (sym (sub0-cont-b2 F₁ f₁))
            (→equalInTypeSUBSING
              (equalTypes-contBody i w2 F₁ F₁ f₁ f₁ (equalInType-mon (equalInType-refl (equalInType-TPURE→ eF)) w2 e2) (equalInType-refl (equalInType-TPURE→ ef)))
              (Mod.∀𝕎-□ M aw3))
          where
            aw3 : ∀𝕎 w2 (λ w' _ → SUBSINGeq (equalInType i w' (#contBody F₁ f₁))
                                              (#APPLY (#APPLY #contExt F₁) f₁)
                                              (#APPLY (#APPLY #contExt F₂) f₂))
            aw3 w3 e3 =
              continuityBody-aux cn exb gc i w3 F₁ f₁
                (Mod.↑□ M (equalInType-TPURE-BAIRE→NATₗ i w1 F₁ F₂ eF) (⊑-trans· e2 e3))
                (Mod.↑□ M (equalInType-TPURE-BAIREₗ i w2 f₁ f₂ ef) e3)
                (equalInType-mon (equalInType-refl (equalInType-TPURE→ eF)) w3 (⊑-trans· e2 e3))
                (equalInType-mon (equalInType-refl (equalInType-TPURE→ ef)) w3 e3) ,
              equalTypes→equalInType
                (TEQsym-equalTypes i w3 (#contBody F₁ f₁) (#contBody F₂ f₂) eqtc)
                (continuityBody-aux cn exb gc i w3 F₂ f₂
                  (Mod.↑□ M (equalInType-TPURE-BAIRE→NATᵣ i w1 F₁ F₂ eF) (⊑-trans· e2 e3))
                  (Mod.↑□ M (equalInType-TPURE-BAIREᵣ i w2 f₁ f₂ ef) e3)
                  (equalInType-mon (equalInType-refl (equalInType-sym (equalInType-TPURE→ eF))) w3 (⊑-trans· e2 e3))
                  (equalInType-mon (equalInType-refl (equalInType-sym (equalInType-TPURE→ ef))) w3 e3))
              where
                eqtc : equalTypes i w3 (#contBody F₁ f₁) (#contBody F₂ f₂)
                eqtc = equalTypes-contBody i w3 F₁ F₂ f₁ f₂ (equalInType-mon (equalInType-TPURE→ eF) w3 (⊑-trans· e2 e3)) (equalInType-mon (equalInType-TPURE→ ef) w3 e3)

    h1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                       → equalInType i w' (#TPURE #BAIRE→NAT) a₁ a₂
                       → equalTypes i w' (sub0 a₁ (#[0]PI (#[0]TPURE #[0]BAIRE)
                                                          (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2))))
                                         (sub0 a₂ (#[0]PI (#[0]TPURE #[0]BAIRE)
                                                          (#[1]SUBSING (#[1]contBody #[3]VAR3 #[3]VAR2)))))
    h1 w1 e1 F₁ F₂ eF =
      ≡CTerm→eqTypes (sym (sub0-cont-b1 F₁)) (sym (sub0-cont-b1 F₂))
        (equalTypes-cont-PI i w1 F₁ F₂ eF)

\end{code}
