\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
--open import Agda.Builtin.Bool
--open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Nat using (ℕ ; suc ; s≤s ; _<_ ; _≤_)
open import Data.Nat.Properties
--open import Agda.Builtin.Nat
--open import Data.Fin using (Fin ; toℕ)
--open import Data.Fin.Properties using (toℕ<n)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
--open import Data.List.Relation.Binary.Subset.Propositional
--open import Data.List.Relation.Binary.Subset.Propositional.Properties
--  using (⊆-refl ; ⊆-trans ; xs⊆x∷xs)
open import Relation.Binary.PropositionalEquality
  using (sym ; cong ; cong₂ ; subst₂)
--open import Data.List using ()
--open import Data.List.Relation.Unary.Any
--open import Data.List.Properties
--open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
--open import Data.List.Membership.Propositional
--open import Data.List.Membership.Propositional.Properties
open import Data.Sum
--open import Relation.Nullary
open import Axiom.Extensionality.Propositional

-- BoxTT imports
open import calculus
open import terms
open import util
open import world
open import mod
open import encode
open import choice
open import compatible
open import progress
open import getChoice
open import choiceExt
open import newChoice

module partial {L : Level}
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
open import barI(W)(M)
open import computation(W)(C)(K)(G)(X)(N)(EC)
  using (#⇛!sameℕ ; _⇛!_at_ ; _⇛_at_ ; _⇓!_at_ ; _⇓_at_ ; _#⇛!_at_ ; #⇛!-trans ; ⇛!-trans ; #⇛!-refl ; ⇓-trans₂ ;
         ⇓!-refl ; ⇛-trans ; stepsT)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (APPLY-LAMBDA⇓)
--  using (→∧≡true)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
  using (SEQ⇛₁)
--open import terms8(W)(C)(K)(G)(X)(N)(EC)
--  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM! ; #⇛!-FST-PAIR ; #⇛!-SND-PAIR)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (∀𝕎-□Func2)
--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--  using (TSext-equalTypes-equalInType ; TEQsym-equalTypes ; TEQrefl-equalTypes ; TEQtrans-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypesNAT ; equalInType-NAT→ ; →equalInType-NAT ; eqTypesPARTIAL← ; equalInType-local ; equalInType-mon ;
         eqTypesSUBSING← ; eqTypes-local ; equalInTypeSUBSING→ ; NUM-equalInType-NAT ; equalInType-FUN ;
         equalInTypePARTIAL→ ; eqTypesUniv ; equalTypes→equalInType-UNIV ; eqTypesEQ←)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-EQ→₁ ; →equalInTypePARTIAL ; →equalInTypeSUBSING)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--  using (→equalInType-NAT!)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (≡→equalInType ; eqTypesEQ→ᵣ ; NATeq-mon)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon ; equalInType-change-level)

open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-EQ)


-- Type of values, where all the values are equal
#N : CTerm
#N = #SUBSING #NAT

𝐒 : CTerm
𝐒 = #PARTIAL #N

eqTypesN : {w : 𝕎·} {i : ℕ} → isType i w #N
eqTypesN {w} {i} = eqTypesSUBSING← eqTypesNAT

isType-𝐒 : (i : ℕ) (w : 𝕎·) → isType i w 𝐒
isType-𝐒 i w = eqTypesPARTIAL← eqTypesN

-- t converges
_↓ : CTerm → CTerm
t ↓ = #EQ t #N0 𝐒

ι : CTerm
ι = #LAMBDA (#[0]EQ #[0]VAR ⌞ #N0 ⌟ ⌞ 𝐒 ⌟)

#APPLY-ι-#⇛! : (w : 𝕎·) (a : CTerm)
             → #APPLY ι a #⇛! a ↓ at w
#APPLY-ι-#⇛! w a w1 e1 = lift c
  where
  e : sub ⌜ a ⌝ (EQ (VAR 0) (NUM 0) ⌜ 𝐒 ⌝) ≡ ⌜ a ↓ ⌝
  e rewrite #shiftUp 0 a | #shiftDown 0 a = →≡EQ refl refl refl

  c : ⌜ #APPLY ι a ⌝ ⇓! ⌜ a ↓ ⌝ at w1
  c rewrite sym e = APPLY-LAMBDA⇓ w1 (EQ (VAR 0) (NUM 0) ⌜ 𝐒 ⌝) ⌜ a ⌝

-- If s converges then t converges
_≼_ : CTerm → CTerm → CTerm
s ≼ t = #FUN (s ↓) (t ↓)

#hasValue-N0 : (w : 𝕎·) → #hasValue #N0 w
#hasValue-N0 w = lift (N0 , tt , 0 , refl)

#hasValue-N : (w : 𝕎·) (k : ℕ) → #hasValue (#NUM k) w
#hasValue-N w k = lift (NUM k , tt , 0 , refl)

isNat : (w : 𝕎·) (t : CTerm) → Set(lsuc(L))
isNat w t = NATeq w t t

□isNat : (w : 𝕎·) (t : CTerm) → Set(lsuc(L))
□isNat w t = □· w (λ w' _ → isNat w' t)

equalInType-N0→ : (i : ℕ) (w : 𝕎·) (a : CTerm)
                → equalInType i w #N a #N0
                → ∈Type i w #NAT a
equalInType-N0→ i w a h =
  equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 (h1 , h2) → h1) (equalInTypeSUBSING→ h))

→equalInType-N0 : (i : ℕ) (w : 𝕎·) (a : CTerm)
                → ∈Type i w #NAT a
                → equalInType i w #N a #N0
→equalInType-N0 i w a h =
  →equalInTypeSUBSING eqTypesNAT (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalInType i w' #NAT) a #N0)
  aw w1 e1  = equalInType-mon h w1 e1 , NUM-equalInType-NAT i w1 0

→∈Type-N : (i : ℕ) (w : 𝕎·) (k : ℕ)
         → ∈Type i w #N (#NUM k)
→∈Type-N i w k =
  →equalInTypeSUBSING eqTypesNAT (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalInType i w' #NAT) (#NUM k) (#NUM k))
  aw w1 e1  = NUM-equalInType-NAT i w1 k , NUM-equalInType-NAT i w1 k

isNat→hasValue : (w : 𝕎·) (t : CTerm)
               → isNat w t
               → #hasValue t w
isNat→hasValue w t (n , c₁ , c₂) =
  lift (NUM n , tt , lower (c₁ w (⊑-refl· w)) )

isNat→∈Nat : (i : ℕ) (w : 𝕎·) (t : CTerm)
           → isNat w t
           → ∈Type i w #NAT t
isNat→∈Nat i w t h = →equalInType-NAT i w t t (Mod.∀𝕎-□ M (λ w1 e1 → NATeq-mon e1 {t} {t} h))

↓→ : (i : ℕ) (w : 𝕎·) (t : CTerm) → inhType i w (t ↓) → □isNat w t
↓→ i w t (a , j) = Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInTypePARTIAL→ (equalInType-EQ→₁ j)))
  where
  aw : ∀𝕎 w (λ w' e' → PARTIALeq (equalInType i w' #N) w' t #N0
                     → □· w' (↑wPred' (λ w'' _ → isNat w'' t) e'))
  aw w1 e1 h with h w1 (⊑-refl· w1)
  ... | h1 , h2 , h3 = Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 t t h4)
    where
    h4 : ∈Type i w1 #NAT t
    h4 = equalInType-N0→ i w1 t (h3 (h2 (#hasValue-N0 w1)))

    aw1 : ∀𝕎 w1  (λ w' e' → NATeq w' t t
                          → ↑wPred' (λ w'' _ → isNat w'' t) e1 w' e')
    aw1 w2 e2 (n , c₁ , c₂) z = n , c₁ , c₁

→↓ : (i : ℕ) (w : 𝕎·) (t : CTerm) → □isNat w t → inhType i w (t ↓)
→↓ i w t j = #AX , →equalInType-EQ (→equalInTypePARTIAL eqTypesN (Mod.∀𝕎-□Func M aw j))
  where
  aw : ∀𝕎 w (λ w' e' → isNat w' t → PARTIALeq (equalInType i w' #N) w' t #N0)
  aw w1 e1 h w2 e2 =
    (λ q → #hasValue-N0 w2) ,
    (λ q → isNat→hasValue w2 t (NATeq-mon e2 {t} {t} h)) ,
    (λ q → →equalInType-N0 i w1 t (isNat→∈Nat i w1 t h))

-- MOVE to utils
≤suc : (n : ℕ) → n ≤ suc n
≤suc 0 = _≤_.z≤n
≤suc (suc n) = _≤_.s≤s (≤suc n)

NUM∈𝐒 : (i : ℕ) (w : 𝕎·) (k : ℕ) → ∈Type i w 𝐒 (#NUM k)
NUM∈𝐒 i w k = →equalInTypePARTIAL eqTypesN (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' _ → PARTIALeq (equalInType i w' #N) w' (#NUM k) (#NUM k))
  aw w1 e1 w2 e2 =
    (λ q → #hasValue-N w2 k) ,
    (λ q → #hasValue-N w2 k) ,
    (λ q → →∈Type-N i w1 k)

↓∈U : (i j : ℕ) (ltj : i < j) (w : 𝕎·) (a₁ a₂ : CTerm)
    → equalInType j w 𝐒 a₁ a₂
    → equalInType j w (#UNIV i) (a₁ ↓) (a₂ ↓)
↓∈U i j ltj w a₁ a₂ a∈ =
  equalTypes→equalInType-UNIV ltj
    (eqTypesEQ←
      (isType-𝐒 i w)
      (equalInType-change-level {i} {j} (≤-trans (≤suc i) ltj) {w} {𝐒} {a₁} {a₂} (isType-𝐒 i w) a∈)
      (NUM∈𝐒 i w 0))

ι∈𝕊→U : (i j : ℕ) (ltj : i < j) (w : 𝕎·) → ∈Type j w (#FUN 𝐒 (#UNIV i)) ι
ι∈𝕊→U i j ltj w =
  equalInType-FUN (isType-𝐒 j w) (eqTypesUniv w j i ltj) aw
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType j w' 𝐒 a₁ a₂
                    → equalInType j w' (#UNIV i) (#APPLY ι a₁) (#APPLY ι a₂))
  aw w1 e1 a₁ a₂ a∈ =
    equalInType-#⇛ₚ-left-right-rev
      {j} {w1} {#UNIV i} {#APPLY ι a₁} {a₁ ↓} {#APPLY ι a₂} {a₂ ↓}
      (#APPLY-ι-#⇛! w1 a₁)
      (#APPLY-ι-#⇛! w1 a₂)
      (↓∈U i j ltj w1 a₁ a₂ a∈)

_⊔_ : CTerm → CTerm → CTerm
a ⊔ b = #SEQ a b

SEQ-val⇓₁ : {w : 𝕎·} {t v : Term} → isValue v → # t → SEQ v t ⇓ t at w
SEQ-val⇓₁ {w} {t} {v} isv #t = 1 , c0
  where
  c0 : stepsT 1 (SEQ v t) w ≡ t
  c0 with isValue⊎ v
  ... | inj₁ x rewrite #shiftUp 0 (ct t #t) | subNotIn v t #t = refl
  ... | inj₂ x = ⊥-elim (x isv)

SEQ-val⇛₁ : {w : 𝕎·} {t v : Term} → isValue v → # t → SEQ v t ⇛ t at w
SEQ-val⇛₁ {w} {t} {v} isv #t w1 e1 = lift (SEQ-val⇓₁ isv #t)

SEQ-val⇛ : {w : 𝕎·} {a b v : Term}
         → isValue v
         → # b
         → a ⇛ v at w
         → SEQ a b ⇛ b at w
SEQ-val⇛ {w} {a} {b} {v} isv #b comp = ⇛-trans (SEQ⇛₁ comp) (SEQ-val⇛₁ isv #b)

→↓⊔ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
    → inhType i w (a ↓)
    → inhType i w (b ↓)
    → inhType i w ((a ⊔ b) ↓)
→↓⊔ i w a b ca cb =
  →↓ i w (a ⊔ b) (∀𝕎-□Func2 aw (↓→ i w a ca) (↓→ i w b cb))
  where
  aw : ∀𝕎 w (λ w' e' → isNat w' a → isNat w' b → isNat w' (#SEQ a b))
  aw w1 e1 (n , c₁ , c₂) (m , d₁ , d₂) =
    m ,
    ⇛-trans (SEQ-val⇛ {w1} {⌜ a ⌝} {⌜ b ⌝} {NUM n} tt (CTerm.closed b) c₁) d₁ ,
    ⇛-trans (SEQ-val⇛ {w1} {⌜ a ⌝} {⌜ b ⌝} {NUM n} tt (CTerm.closed b) c₁) d₁

-- Not quite what we want. We need ⊔ to force a to compute to always the same number.
↓⊔→ₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
     → inhType i w ((a ⊔ b) ↓)
     → inhType i w (a ↓)
↓⊔→ₗ i w a b j =
  →↓ i w a (Mod.∀𝕎-□Func M aw (↓→ i w (a ⊔ b) j))
  where
  aw : ∀𝕎 w (λ w' e' → isNat w' (#SEQ a b) → isNat w' a)
  aw w1 e1 (n , c₁ , c₂) = {!!}

↓⊔→ᵣ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
     → inhType i w ((a ⊔ b) ↓)
     → inhType i w (b ↓)
↓⊔→ᵣ i w a b j = {!!}

\end{code}
