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
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (∧≡true→ₗ ; ∧≡true→ᵣ ; APPLY⇓ ; hasValueℕ ; hasValue-APPLY→)
--open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (¬Names→steps ; ¬Names→⇓)
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


#¬Names→#⇛!ₙ : (w : 𝕎·) {a : CTerm}
             → #¬Names a
             → #¬Enc a
             → #⇛!ₙ a w
#¬Names→#⇛!ₙ w {a} nn ne = a , #⇛!-refl {w} {a} , nn , ne


→equalInType-TPURE : {i : ℕ} {w : 𝕎·} {T a b : CTerm}
                      → #¬Names a
                      → #¬Names b
                      → #¬Enc a
                      → #¬Enc b
                      → equalInType i w T a b
                      → equalInType i w (#TPURE T) a b
→equalInType-TPURE {i} {w} {T} {a} {b} nna nnb nea neb a∈ =
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
        aw2 : ∀𝕎 w1 (λ w' _ → PUREeq w' a b)
        aw2 w2 e2 = #¬Names→#⇛!ₙ w2 {a} nna nea , #¬Names→#⇛!ₙ w2 {b} nnb neb --lift (nna , nnb)


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
                      → □· w (λ w' e → #⇛!ₙ a w') --#¬Names a
equalInType-TPURE→ₗ {i} {w} {T} {a} {b} eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b
                       → □· w' (↑wPred' (λ w'' e → #⇛!ₙ a w'') e'))
    aw w1 e1 (eqa , eqb) = Mod.∀𝕎-□Func M (λ w1 e1 h z → fst h) (equalInType-PURE→ eqb)

    h : □· w (λ w' _ → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TPURE≡ T) eqi)


equalInType-TPURE→ᵣ : {i : ℕ} {w : 𝕎·} {T a b : CTerm}
                      → equalInType i w (#TPURE T) a b
                      → □· w (λ w' e → #⇛!ₙ b w') --#¬Names b
equalInType-TPURE→ᵣ {i} {w} {T} {a} {b} eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b
                       → □· w' (↑wPred' (λ w'' e → #⇛!ₙ b w'') e'))
    aw w1 e1 (eqa , eqb) = Mod.∀𝕎-□Func M (λ w1 e1 h z → snd h) (equalInType-PURE→ eqb)

    h : □· w (λ w' _ → ISECTeq (equalInType i w' T) (equalInType i w' #PURE) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TPURE≡ T) eqi)


sub0-#[0]TPURE : (a : CTerm) (b : CTerm0)
                 → sub0 a (#[0]TPURE b) ≡ #TPURE (sub0 a b)
sub0-#[0]TPURE a b = CTerm≡ refl


{--
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
--}


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
BOOLₚ = TPURE BOOL₀


-- MOVE
#BOOLₚ : CTerm
#BOOLₚ = ct BOOLₚ refl


-- MOVE
#BOOLₚ≡ : #BOOLₚ ≡ #TPURE #BOOL₀
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
isTypeBOOLₚ {w} {i} = equalTypesTPURE isTypeBOOL₀


→equalInType-BOOLₚ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → #¬Names a
                      → #¬Names b
                      → #¬Enc a
                      → #¬Enc b
                      → equalInType i w #BOOL₀ a b
                      → equalInType i w #BOOLₚ a b
→equalInType-BOOLₚ i w a b nna nnb nea neb h =
  ≡CTerm→equalInType (sym #BOOLₚ≡) (→equalInType-TPURE nna nnb nea neb h)


equalInType-BOOLₚ→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #BOOLₚ a b
                      → □· w (λ w' _ → #strongBool w' a b)
equalInType-BOOLₚ→ i w a b h = equalInType-BOOL₀→strongBool i w a b (equalInType-TPURE→ h)


equalInType-BOOLₚ→ₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #BOOLₚ a b
                      → □· w (λ w' e → #⇛!ₙ a w') --#¬Names a
equalInType-BOOLₚ→ₗ i w a b h = equalInType-TPURE→ₗ h


equalInType-BOOLₚ→ᵣ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #BOOLₚ a b
                      → □· w (λ w' e → #⇛!ₙ b w')  --#¬Names b
equalInType-BOOLₚ→ᵣ i w a b h = equalInType-TPURE→ᵣ h


BTRUE∈BOOLₚ : (i : ℕ) (w : 𝕎·)
               → ∈Type i w #BOOLₚ #BTRUE
BTRUE∈BOOLₚ i w = →equalInType-BOOLₚ i w #BTRUE #BTRUE refl refl refl refl (BTRUE∈BOOL₀ i w)


BFALSE∈BOOLₚ : (i : ℕ) (w : 𝕎·)
                   → ∈Type i w #BOOLₚ #BFALSE
BFALSE∈BOOLₚ i w = →equalInType-BOOLₚ i w #BFALSE #BFALSE refl refl refl refl (BFALSE∈BOOL₀ i w)


{--
#⇛!ₙ a w
a ⇓ v from w
a ⇓! v from w
--}


APPLY-ID⇛₀ : (w : 𝕎·) (a : Term)
          → APPLY ID a ⇛ a at w
APPLY-ID⇛₀ w a w1 e1 = lift (1 , c)
  where
  c : stepsT 1 (APPLY ID a) w1 ≡ a
  c rewrite shiftDownUp a 0 = refl


APPLY-ID⇛ : (w : 𝕎·) (a v : Term)
          → a ⇛ v at w
          → APPLY ID a ⇛ v at w
APPLY-ID⇛ w a v comp = ⇛-trans {w} {APPLY ID a} {a} {v} (APPLY-ID⇛₀ w a) comp


ID∈BAIRE : (i : ℕ) (w : 𝕎·)
         → equalInType i w #BAIRE #ID #ID
ID∈BAIRE i w =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                    → equalInType i w' #NAT (#APPLY #ID a₁) (#APPLY #ID a₂))
  aw w1 e1 a₁ a₂ a∈ =
    →equalInType-NAT i w1 (#APPLY #ID a₁) (#APPLY #ID a₂) (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ a∈))
    where
    aw1 : ∀𝕎 w1 (λ w' e' → #strongMonEq w' a₁ a₂
                         → #strongMonEq w' (#APPLY #ID a₁) (#APPLY #ID a₂))
    aw1 w2 e2 (n , c₁ , c₂) = n , APPLY-ID⇛ w2 ⌜ a₁ ⌝ (NUM n) c₁ , APPLY-ID⇛ w2 ⌜ a₂ ⌝ (NUM n) c₂


#⇛!nv : (a : CTerm) (w : 𝕎·) → Set(lsuc(L))
#⇛!nv a w = Σ CTerm (λ b → a #⇛! b at w × #¬Names b × #¬Enc b × #isValue b)


#⇛v : (a : CTerm) (w : 𝕎·) → Set(lsuc(L))
#⇛v a w = Σ CTerm (λ b → a #⇛ b at w × #isValue b)


equalInType-NAT→#⇛vₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #NAT a b
                     → □· w (λ w' e → #⇛v a w')
equalInType-NAT→#⇛vₗ i w a b a∈ =
  Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w a b a∈)
  where
  aw : ∀𝕎 w (λ w' e' → #strongMonEq w' a b → #⇛v a w')
  aw w1 e1 (n , c₁ , c₂) = #NUM n , c₁ , tt


equalInType-NAT→#⇛vᵣ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #NAT a b
                     → □· w (λ w' e → #⇛v b w')
equalInType-NAT→#⇛vᵣ i w a b a∈ =
  Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w a b a∈)
  where
  aw : ∀𝕎 w (λ w' e' → #strongMonEq w' a b → #⇛v b w')
  aw w1 e1 (n , c₁ , c₂) = #NUM n , c₂ , tt


→#⇛!-APPLY : {w : 𝕎·} {F G a : CTerm}
           → F #⇛! G at w
           → #APPLY F a #⇛! #APPLY G a at w
→#⇛!-APPLY {w} {F} {G} {A} comp w1 e1 =
  lift (APPLY⇓ {w1} {w1} {⌜ F ⌝} {⌜ G ⌝} ⌜ A ⌝ (lower (comp w1 e1)))


{--
#⇛v-#APPLY→ : (w : 𝕎·) (f a : CTerm)
            → #⇛v (#APPLY f a) w
            → #⇛v f w
#⇛v-#APPLY→ w f a (v , comp , isv) = {!!}


□#⇛v-#APPLY→ : (w : 𝕎·) (f a : CTerm)
            → □· w (λ w' e → #⇛v (#APPLY f a) w')
            → □· w (λ w' e → #⇛v f w')
□#⇛v-#APPLY→ w f a comp = Mod.∀𝕎-□Func M (λ w1 e1 → #⇛v-#APPLY→ w1 f a) comp
--}


steps→# : (t v : Term) (w w' : 𝕎·) (n : ℕ)
        → # t
        → ¬Names t
        → ¬Enc t
        → steps n (t , w) ≡ (v , w')
        → # v
steps→# t v w w' n #t nnt net comp = ⊆[]→≡[] (⊆-trans ss (≡[]→⊆[] #t))
  where
  ss : fvars v ⊆ fvars t
  ss = snd (snd (snd (snd (¬Names→steps n w w' w t v nnt comp))) net)


#hasValueℕ→ΣCTerm : (t : Term) (w : 𝕎·) (n : ℕ)
                  → # t
                  → ¬Names t
                  → ¬Enc t
                  → hasValueℕ n t w
                  → Σ Term (λ u → # u × isValue u × ¬Names u × ¬Enc u × Σ 𝕎· (λ w' → t ⇓ u from w to w'))
#hasValueℕ→ΣCTerm t w n #t nnt net (v , w' , comp , isv) =
  v , steps→# t v w w' n #t nnt net comp , isv ,
  fst (snd (snd (¬Names→steps n w w' w t v nnt comp))) ,
  fst (snd (snd (snd (¬Names→steps n w w' w t v nnt comp))) net) ,
  w' , (n , comp)


APPLY#⇛→#⇛!nv : {w : 𝕎·} {f a v : CTerm}
              → #isValue v
              → #¬Names f
              → #¬Enc f
              → #APPLY f a #⇛ v at w
              → #⇛!nv f w
APPLY#⇛→#⇛!nv {w} {f} {a} {v} isv nn ne comp =
  ct (fst c2) (fst (snd c2)) ,
  c3 ,
  fst (snd (snd (snd c2))) ,
  fst (snd (snd (snd (snd c2)))) ,
  fst (snd (snd c2))
  where
  c1 : Σ 𝕎· (λ w' → #APPLY f a #⇓ v from w to w')
  c1 = #⇓→from-to {w} {#APPLY f a} {v} (lower (comp w (⊑-refl· w)))

  hv : hasValueℕ (fst (snd c1)) ⌜ f ⌝ w
  hv = hasValue-APPLY→ ⌜ f ⌝ ⌜ a ⌝ w {fst (snd c1)}
         (⌜ v ⌝ , fst c1 , snd (snd c1) , isv)

  c2 : Σ Term (λ g → # g × isValue g × ¬Names g × ¬Enc g × Σ 𝕎· (λ w' → ⌜ f ⌝ ⇓ g from w to w'))
  c2 = #hasValueℕ→ΣCTerm ⌜ f ⌝ w (fst (snd c1)) (CTerm.closed f) nn ne hv

  c3 : ⌜ f ⌝ ⇛! fst c2 at w
  c3 w1 e1 = lift (fst (snd (snd (snd (snd (snd (snd c2)))))) ,
                   fst (¬Names→steps (fst (snd (snd (snd (snd (snd (snd c2))))))) w
                                     (fst (snd (snd (snd (snd (snd c2)))))) w1 ⌜ f ⌝ (fst c2)
                                     nn (snd (snd (snd (snd (snd (snd (snd c2)))))))))


#⇛!-pres-#⇛!nv : {w : 𝕎·} {F K : CTerm}
               → F #⇛! K at w
               → #⇛!nv K w
               → #⇛!nv F w
#⇛!-pres-#⇛!nv {w} {F} {K} comp (b , c , nn , ne , isv) =
  b , #⇛!-trans {w} {F} {K} {b} comp c , nn , ne , isv


equalInType-TPURE-BAIRE→NATₗ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                             → equalInType i w (#TPURE #BAIRE→NAT) F G
                             → □· w (λ w' e → #⇛!nv F w')
equalInType-TPURE-BAIRE→NATₗ i w F G F∈ =
  ∀𝕎-□Func2 aw h2 h3
  where
  h1 : equalInType i w #BAIRE→NAT F G
  h1 = equalInType-TPURE→ F∈

  h2 : □· w (λ w' e → #⇛v (#APPLY F #ID) w')
  h2 = equalInType-NAT→#⇛vₗ i w (#APPLY F #ID) (#APPLY G #ID)
         (equalInType-FUN→ (≡CTerm→equalInType #BAIRE→NAT≡ h1) w (⊑-refl· w) #ID #ID (ID∈BAIRE i w))

  h3 : □· w (λ w' e → #⇛!ₙ F w')
  h3 = equalInType-TPURE→ₗ F∈

  aw  : ∀𝕎 w (λ w' e' → #⇛v (#APPLY F #ID) w' → #⇛!ₙ F w' → #⇛!nv F w')
  aw w1 e1 (v , c , isv) (K , d , nn , ne) =
    #⇛!-pres-#⇛!nv {w1} {F} {K} d c2
    where
    c1 : #APPLY K #ID #⇛ v at w1
    c1 = val-#⇛→ {w1} {#APPLY F #ID} {#APPLY K #ID} {v} isv (→#⇛!-APPLY {w1} {F} {K} {#ID} d) c

    c2 : #⇛!nv K w1
    c2 = APPLY#⇛→#⇛!nv {w1} {K} {#ID} {v} isv nn ne c1


equalInType-TPURE-BAIRE→NATᵣ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                             → equalInType i w (#TPURE #BAIRE→NAT) F G
                             → □· w (λ w' e → #⇛!nv G w')
equalInType-TPURE-BAIRE→NATᵣ i w F G F∈ =
  ∀𝕎-□Func2 aw h2 h3
  where
  h1 : equalInType i w #BAIRE→NAT F G
  h1 = equalInType-TPURE→ F∈

  h2 : □· w (λ w' e → #⇛v (#APPLY G #ID) w')
  h2 = equalInType-NAT→#⇛vᵣ i w (#APPLY F #ID) (#APPLY G #ID)
         (equalInType-FUN→ (≡CTerm→equalInType #BAIRE→NAT≡ h1) w (⊑-refl· w) #ID #ID (ID∈BAIRE i w))

  h3 : □· w (λ w' e → #⇛!ₙ G w')
  h3 = equalInType-TPURE→ᵣ F∈

  aw  : ∀𝕎 w (λ w' e' → #⇛v (#APPLY G #ID) w' → #⇛!ₙ G w' → #⇛!nv G w')
  aw w1 e1 (v , c , isv) (K , d , nn , ne) =
    #⇛!-pres-#⇛!nv {w1} {G} {K} d c2
    where
    c1 : #APPLY K #ID #⇛ v at w1
    c1 = val-#⇛→ {w1} {#APPLY G #ID} {#APPLY K #ID} {v} isv (→#⇛!-APPLY {w1} {G} {K} {#ID} d) c

    c2 : #⇛!nv K w1
    c2 = APPLY#⇛→#⇛!nv {w1} {K} {#ID} {v} isv nn ne c1


equalInType-TPURE-BAIREₗ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                             → equalInType i w (#TPURE #BAIRE) F G
                             → □· w (λ w' e → #⇛!nv F w')
equalInType-TPURE-BAIREₗ i w F G F∈ =
  ∀𝕎-□Func2 aw h2 h3
  where
  h1 : equalInType i w #BAIRE F G
  h1 = equalInType-TPURE→ F∈

  h2 : □· w (λ w' e → #⇛v (#APPLY F #N0) w')
  h2 = equalInType-NAT→#⇛vₗ i w (#APPLY F #N0) (#APPLY G #N0)
         (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ h1) w (⊑-refl· w) #N0 #N0 (NUM-equalInType-NAT i w 0))

  h3 : □· w (λ w' e → #⇛!ₙ F w')
  h3 = equalInType-TPURE→ₗ F∈

  aw  : ∀𝕎 w (λ w' e' → #⇛v (#APPLY F #N0) w' → #⇛!ₙ F w' → #⇛!nv F w')
  aw w1 e1 (v , c , isv) (K , d , nn , ne) =
    #⇛!-pres-#⇛!nv {w1} {F} {K} d c2
    where
    c1 : #APPLY K #N0 #⇛ v at w1
    c1 = val-#⇛→ {w1} {#APPLY F #N0} {#APPLY K #N0} {v} isv (→#⇛!-APPLY {w1} {F} {K} {#N0} d) c

    c2 : #⇛!nv K w1
    c2 = APPLY#⇛→#⇛!nv {w1} {K} {#N0} {v} isv nn ne c1


equalInType-TPURE-BAIREᵣ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                             → equalInType i w (#TPURE #BAIRE) F G
                             → □· w (λ w' e → #⇛!nv G w')
equalInType-TPURE-BAIREᵣ i w F G F∈ =
  ∀𝕎-□Func2 aw h2 h3
  where
  h1 : equalInType i w #BAIRE F G
  h1 = equalInType-TPURE→ F∈

  h2 : □· w (λ w' e → #⇛v (#APPLY G #N0) w')
  h2 = equalInType-NAT→#⇛vᵣ i w (#APPLY F #N0) (#APPLY G #N0)
         (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ h1) w (⊑-refl· w) #N0 #N0 (NUM-equalInType-NAT i w 0))

  h3 : □· w (λ w' e → #⇛!ₙ G w')
  h3 = equalInType-TPURE→ᵣ F∈

  aw  : ∀𝕎 w (λ w' e' → #⇛v (#APPLY G #N0) w' → #⇛!ₙ G w' → #⇛!nv G w')
  aw w1 e1 (v , c , isv) (K , d , nn , ne) =
    #⇛!-pres-#⇛!nv {w1} {G} {K} d c2
    where
    c1 : #APPLY K #N0 #⇛ v at w1
    c1 = val-#⇛→ {w1} {#APPLY G #N0} {#APPLY K #N0} {v} isv (→#⇛!-APPLY {w1} {G} {K} {#N0} d) c

    c2 : #⇛!nv K w1
    c2 = APPLY#⇛→#⇛!nv {w1} {K} {#N0} {v} isv nn ne c1


#⇛!→equalInTypeᵣ : {i : ℕ} {w : 𝕎·} {T F G : CTerm}
                 → ∈Type i w T F
                 → F #⇛! G at w
                 → equalInType i w T F G
#⇛!→equalInTypeᵣ {i} {w} {T} {F} {G} F∈ cF =
  equalInType-#⇛-LR {i} {w} {T} {F} {F} {F} {G} (#⇛!-refl {w} {F}) cF F∈


#⇛!→∈Type : {i : ℕ} {w : 𝕎·} {T F G : CTerm}
          → ∈Type i w T F
          → F #⇛! G at w
          → ∈Type i w T G
#⇛!→∈Type {i} {w} {T} {F} {G} F∈ comp =
  equalInType-#⇛-LR {i} {w} {T} {F} {G} {F} {G} comp comp F∈


#⇛!→equalInType : {i : ℕ} {w : 𝕎·} {T F₁ F₂ G₁ G₂ : CTerm}
                → equalInType i w T F₁ F₂
                → F₁ #⇛! G₁ at w
                → F₂ #⇛! G₂ at w
                → equalInType i w T G₁ G₂
#⇛!→equalInType {i} {w} {T} {F₁} {F₂} {G₁} {G₂} F∈ comp₁ comp₂ =
  equalInType-#⇛-LR {i} {w} {T} {F₁} {G₁} {F₂} {G₂} comp₁ comp₂ F∈

\end{code}
