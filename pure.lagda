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


module pure {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
            (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
            (X : ChoiceExt W C)
            (N : NewChoice {L} W C K G)
            (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
            (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC) using (∧≡true→ₗ ; ∧≡true→ᵣ)
--open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC) using (¬Names→steps ; ¬Names→⇓)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
--open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)


¬Names→⇓→⇛ : (w w' : 𝕎·) (t u : Term)
               → ¬Names t
               → t ⇓ u at w
               → t ⇛ u at w
¬Names→⇓→⇛ w w' t u nnt comp w1 e1 =
  lift (⇓-from-to→⇓ {w1} {w1} (fst (snd h) , fst (¬Names→steps (fst (snd h)) w (fst h) w1 t u nnt (snd (snd h)))))
  where
    h : Σ 𝕎· (λ w' → t ⇓ u from w to w')
    h = ⇓→from-to comp


¬Names→⇛ : (w1 w2 : 𝕎·) (t u : Term)
            → ¬Names t
            → t ⇛ u at w1
            → t ⇛ u at w2
¬Names→⇛ w1 w2 t u nnt comp w e =
  lift (⇓-from-to→⇓ {w} {w} (¬Names→⇓ w1 (fst h) w t u nnt (snd h)))
  where
    h : Σ 𝕎· (λ w' → t ⇓ u from w1 to w')
    h = ⇓→from-to (lower (comp w1 (⊑-refl· w1)))


¬Names→⇛! : (w1 w2 : 𝕎·) (t u : Term)
            → ¬Names t
            → t ⇛! u at w1
            → t ⇛! u at w2
¬Names→⇛! w1 w2 t u nnt comp w e =
  lift (¬Names→⇓ w1 w1 w t u nnt (lower (comp w1 (⊑-refl· w1))))


#¬Names-APPLY : {a b : CTerm} → #¬Names a → #¬Names b → #¬Names (#APPLY a b)
#¬Names-APPLY {a} {b} nna nnb rewrite nna | nnb = refl


#¬Names-APPLY→ₗ : {a b : CTerm} → #¬Names (#APPLY a b) → #¬Names a
#¬Names-APPLY→ₗ {a} {b} nna = ∧≡true→ₗ (#¬names a) (#¬names b) nna


#¬Names-APPLY→ᵣ : {a b : CTerm} → #¬Names (#APPLY a b) → #¬Names b
#¬Names-APPLY→ᵣ {a} {b} nna = ∧≡true→ᵣ (#¬names a) (#¬names b) nna


#TPURE≡ : (T : CTerm) → #TPURE T ≡ #ISECT T #PURE
#TPURE≡ T = CTerm≡ refl


equalTypesTPURE : {i : ℕ} {w : 𝕎·} {A B : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w (#TPURE A) (#TPURE B)
equalTypesTPURE {i} {w} {A} {B} eqt =
  ≡CTerm→eqTypes
    (sym (#TPURE≡ A))
    (sym (#TPURE≡ B))
    (eqTypesISECT← eqt eqTypesPURE←)


→equalInType-TPURE : {i : ℕ} {w : 𝕎·} {T a b : CTerm}
                      → #¬Names a
                      → #¬Names b
                      → equalInType i w T a b
                      → equalInType i w (#TPURE T) a b
→equalInType-TPURE {i} {w} {T} {a} {b} nna nnb a∈ =
  ≡CTerm→equalInType
    (sym (#TPURE≡ T))
    (→equalInType-ISECT
      (fst a∈)
      (eqTypesPURE← {w} {i})
      (Mod.∀𝕎-□ M aw1))
  where
    aw1 : ∀𝕎 w (λ w' _ → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b)
    aw1 w1 e1 = equalInType-mon a∈ w1 e1 , →equalInTypePURE (Mod.∀𝕎-□ M aw2)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → PUREeq a b)
        aw2 w2 e2 = lift (nna , nnb)


equalInType-TPURE→ : {i : ℕ} {w : 𝕎·} {T a b : CTerm}
                      → equalInType i w (#TPURE T) a b
                      → equalInType i w T a b
equalInType-TPURE→ {i} {w} {T} {a} {b} eqi =
  equalInType-local (Mod.∀𝕎-□Func M (λ w' e (h1 , h2) → h1) h)
  where
    h : □· w (λ w' _ → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TPURE≡ T) eqi)



equalInType-TPURE→ₗ : {i : ℕ} {w : 𝕎·} {T a b : CTerm}
                      → equalInType i w (#TPURE T) a b
                      → #¬Names a
equalInType-TPURE→ₗ {i} {w} {T} {a} {b} eqi =
  lower (Mod.□-const M {w} {Lift {0ℓ} (lsuc L) (#¬Names a)} (Mod.∀𝕎-□Func M aw h))
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b
                        → Lift (lsuc L) (#¬Names a))
    aw w1 e1 (eqa , eqb) = Mod.□-const M {w1} {Lift {0ℓ} (lsuc L) (#¬Names a)} (Mod.∀𝕎-□Func M (λ w2 e2 (lift (h1 , h2)) → lift h1) (equalInType-PURE→ eqb))

    h : □· w (λ w' _ → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TPURE≡ T) eqi)



equalInType-TPURE→ᵣ : {i : ℕ} {w : 𝕎·} {T a b : CTerm}
                      → equalInType i w (#TPURE T) a b
                      → #¬Names b
equalInType-TPURE→ᵣ {i} {w} {T} {a} {b} eqi =
  lower (Mod.□-const M {w} {Lift {0ℓ} (lsuc L) (#¬Names b)} (Mod.∀𝕎-□Func M aw h))
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b
                        → Lift (lsuc L) (#¬Names b))
    aw w1 e1 (eqa , eqb) = Mod.□-const M {w1} {Lift {0ℓ} (lsuc L) (#¬Names b)} (Mod.∀𝕎-□Func M (λ w2 e2 (lift (h1 , h2)) → lift h2) (equalInType-PURE→ eqb))

    h : □· w (λ w' _ → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TPURE≡ T) eqi)


sub0-#[0]TPURE : (a : CTerm) (b : CTerm0)
                 → sub0 a (#[0]TPURE b) ≡ #TPURE (sub0 a b)
sub0-#[0]TPURE a b = CTerm≡ refl


∈pure-PI→ : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {a b : CTerm}
              → equalInType i w (#TPURE (#PI A B)) a b
              → equalInType i w (#PI (#TPURE A) (#[0]TPURE B)) a b
∈pure-PI→ {i} {w} {A} {B} {a} {b} a∈ =
  equalInType-PI
    {i} {w} {#TPURE A} {#[0]TPURE B} {a} {b}
    (λ w1 e1 → equalTypesTPURE (fst (equalInType-PI→ {i} {w1} {A} {B} {a} {b} (equalInType-mon b∈ w1 e1))))
    h1
    h2
  where
    b∈ : equalInType i w (#PI A B) a b
    b∈ = equalInType-TPURE→ a∈

    h1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#TPURE A) a₁ a₂
                       → equalTypes i w' (sub0 a₁ (#[0]TPURE B)) (sub0 a₂ (#[0]TPURE B)))
    h1 w1 e1 a₁ a₂ x =
      ≡CTerm→eqTypes
        (sym (sub0-#[0]TPURE a₁ B)) (sym (sub0-#[0]TPURE a₂ B))
        (equalTypesTPURE
          (fst (snd (equalInType-PI→ {i} {w1} {A} {B} {a} {b} (equalInType-mon b∈ w1 e1)))
               w1 (⊑-refl· w1) a₁ a₂ (equalInType-TPURE→ x)))

    h2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#TPURE A) a₁ a₂
                       → equalInType i w' (sub0 a₁ (#[0]TPURE B)) (#APPLY a a₁) (#APPLY b a₂))
    h2 w1 e1 a₁ a₂ x =
      ≡CTerm→equalInType
        (sym (sub0-#[0]TPURE a₁ B))
        (→equalInType-TPURE
          (#¬Names-APPLY {a} {a₁} (equalInType-TPURE→ₗ {i} {w} {#PI A B} {a} {b} a∈) (equalInType-TPURE→ₗ {i} {w1} {A} {a₁} {a₂} x))
          (#¬Names-APPLY {b} {a₂} (equalInType-TPURE→ᵣ {i} {w} {#PI A B} {a} {b} a∈) (equalInType-TPURE→ᵣ {i} {w1} {A} {a₁} {a₂} x))
          (snd (snd (equalInType-PI→ {i} {w1} {A} {B} {a} {b} (equalInType-mon b∈ w1 e1))) w1 (⊑-refl· w1) a₁ a₂ (equalInType-TPURE→ x)))


-- We can prove that a and b are pure if (#TPURE A) is pointed, but this is not true in general because we can't prove:
--        ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂
--                      → equalInType i w' (sub0 a₁ B) (#APPLY a a₁) (#APPLY b a₂))
{--
→∈pure-PI : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {a b x : CTerm}
              → ∈Type i w (#TPURE A) x
              → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
              → equalInType i w (#PI (#TPURE A) (#[0]TPURE B)) a b
              → equalInType i w (#TPURE (#PI A B)) a b
→∈pure-PI {i} {w} {A} {B} {a} {b} {x} x∈ funcB a∈ =
  →equalInType-TPURE
    (#¬Names-APPLY→ₗ {a} {x} (equalInType-TPURE→ₗ y∈))
    (#¬Names-APPLY→ₗ {b} {x} (equalInType-TPURE→ᵣ y∈))
    (equalInType-PI
      (λ w1 e1 → fst (equalInType-mon (equalInType-TPURE→ x∈) w1 e1))
      funcB
      aw1)
  where
    y∈ : equalInType i w (#TPURE (sub0 x B)) (#APPLY a x) (#APPLY b x)
    y∈ =
      ≡CTerm→equalInType
        (sub0-#[0]TPURE x B)
        (snd (snd (equalInType-PI→ {i} {w} {#TPURE A} {#[0]TPURE B} {a} {b} a∈)) w (⊑-refl· w) x x x∈)

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂
                        → equalInType i w' (sub0 a₁ B) (#APPLY a a₁) (#APPLY b a₂))
    aw1 w1 e1 a₁ a₂ z = {!!}
--}


-- MOVE
BOOLₚ : Term
BOOLₚ = TPURE BOOL


-- MOVE
#BOOLₚ : CTerm
#BOOLₚ = ct BOOLₚ refl


-- MOVE
#BOOLₚ≡ : #BOOLₚ ≡ #TPURE #BOOL
#BOOLₚ≡ = CTerm≡ refl


-- MOVE
#[0]BOOLₚ : CTerm0
#[0]BOOLₚ = ct0 BOOLₚ refl


-- MOVE
NATₚ : Term
NATₚ = TPURE NAT


-- MOVE
#NATₚ : CTerm
#NATₚ = ct NATₚ refl


-- MOVE
#NATₚ≡ : #NATₚ ≡ #TPURE #NAT
#NATₚ≡ = CTerm≡ refl


-- MOVE
#[0]NATₚ : CTerm0
#[0]NATₚ = ct0 NATₚ refl


isTypeNATₚ : {w : 𝕎·} {i : ℕ} → isType i w #NATₚ
isTypeNATₚ {w} {i} = equalTypesTPURE eqTypesNAT


isTypeBOOLₚ : {w : 𝕎·} {i : ℕ} → isType i w #BOOLₚ
isTypeBOOLₚ {w} {i} = equalTypesTPURE (isTypeBOOL w i)


→equalInType-BOOLₚ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → #¬Names a
                      → #¬Names b
                      → equalInType i w #BOOL a b
                      → equalInType i w #BOOLₚ a b
→equalInType-BOOLₚ i w a b nna nnb h =
  ≡CTerm→equalInType (sym #BOOLₚ≡) (→equalInType-TPURE nna nnb h)


equalInType-BOOLₚ→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #BOOLₚ a b
                      → □· w (λ w' _ → #strongBool w' a b)
equalInType-BOOLₚ→ i w a b h = equalInType-BOOL→ i w a b (equalInType-TPURE→ h)


equalInType-BOOLₚ→ₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #BOOLₚ a b
                      → #¬Names a
equalInType-BOOLₚ→ₗ i w a b h = equalInType-TPURE→ₗ h


equalInType-BOOLₚ→ᵣ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #BOOLₚ a b
                      → #¬Names b
equalInType-BOOLₚ→ᵣ i w a b h = equalInType-TPURE→ᵣ h


BTRUE∈BOOLₚ : (i : ℕ) (w : 𝕎·)
               → ∈Type i w #BOOLₚ #BTRUE
BTRUE∈BOOLₚ i w = →equalInType-BOOLₚ i w #BTRUE #BTRUE refl refl (BTRUE∈BOOL i w)


BFALSE∈BOOLₚ : (i : ℕ) (w : 𝕎·)
                   → ∈Type i w #BOOLₚ #BFALSE
BFALSE∈BOOLₚ i w = →equalInType-BOOLₚ i w #BFALSE #BFALSE refl refl (BFALSE∈BOOL i w)

\end{code}
