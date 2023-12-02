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
open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
--open import Data.List.Membership.Propositional
--open import Data.List.Membership.Propositional.Properties
open import Data.Sum
open import Relation.Nullary
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
open import Axiom.ExcludedMiddle

module partial {L  : Level}
               (W  : PossibleWorlds {L})
               (M  : Mod W)
               (C  : Choice)
               (K  : Compatible {L} W C)
               (P  : Progress {L} W C K)
               (G  : GetChoice {L} W C K)
               (X  : ChoiceExt W C)
               (N  : NewChoice W C K G)
               (E  : Extensionality 0ℓ (lsuc(lsuc(L))))
               (EC : Encode)
               (EM : ExcludedMiddle (L))
       where

open import worldDef(W)
open import barI(W)(M)
open import computation(W)(C)(K)(G)(X)(N)(EC)
  using (#⇛!sameℕ ; _⇛!_at_ ; _⇛_at_ ; _⇓!_at_ ; _⇓_at_ ; _⇓_from_to_ ; _#⇛!_at_ ; #⇛!-trans ; ⇛!-trans ; #⇛!-refl ;
         ⇓-trans₂ ; ⇓!-refl ; ⇛-trans ; stepsT ; steps ; #weakMonEq! ; ⇓!→⇓ ; stepsVal ; step⊎ ; step-⇓-from-to-trans ;
         ⇓-from-to→⇓)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (APPLY-LAMBDA⇓ ; hasValue ; LET→hasValue)
--  using (→∧≡true)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (sub-shiftUp0≡)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
  using (SEQ⇛₁ ; SEQ⇓₁)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM! ; #⇛!-FST-PAIR ; #⇛!-SND-PAIR)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (∀𝕎-□Func2)
--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--  using (TSext-equalTypes-equalInType ; TEQsym-equalTypes ; TEQrefl-equalTypes ; TEQtrans-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypesNAT ; equalInType-NAT→ ; →equalInType-NAT ; eqTypesPARTIAL← ; equalInType-local ; equalInType-mon ;
         eqTypesSUBSING← ; eqTypes-local ; equalInTypeSUBSING→ ; NUM-equalInType-NAT ; equalInType-FUN ;
         equalInTypePARTIAL→ ; eqTypesUniv ; equalTypes→equalInType-UNIV ; eqTypesEQ← ; NUM-equalInType-QNAT! ;
         equalInType-QNAT!→ ; →equalInType-QNAT! ; equalInType-refl)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-EQ→₁ ; →equalInTypePARTIAL ; →equalInTypeSUBSING ; eqTypesQNAT!)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--  using (→equalInType-NAT!)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (≡→equalInType ; eqTypesEQ→ᵣ ; NATeq-mon ; #PROD)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon ; equalInType-change-level)

open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-EQ)


𝐕 : CTerm
𝐕 = #QNAT!

-- Type of values, where all the values are equal
𝟙 : CTerm
𝟙 = #SUBSING 𝐕

𝐒 : CTerm
𝐒 = #PARTIAL 𝟙

𝕦 : CTerm
𝕦 = #N0

eqTypesN : {w : 𝕎·} {i : ℕ} → isType i w 𝟙
eqTypesN {w} {i} = eqTypesSUBSING← eqTypesQNAT!

isType-𝐒 : (i : ℕ) (w : 𝕎·) → isType i w 𝐒
isType-𝐒 i w = eqTypesPARTIAL← eqTypesN

-- t converges
_↓ : CTerm → CTerm
t ↓ = #EQ t 𝕦 𝐒

_↓₀ : CTerm0 → CTerm0
t ↓₀ = #[0]EQ t ⌞ 𝕦 ⌟ ⌞ 𝐒 ⌟

-- λ x → x ↓
ι : CTerm
ι = #LAMBDA (#[0]EQ #[0]VAR ⌞ 𝕦 ⌟ ⌞ 𝐒 ⌟)

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

#hasValue-N0 : (w : 𝕎·) → #hasValue 𝕦 w
#hasValue-N0 w = lift (N0 , tt , 0 , refl)

#hasValue-N : (w : 𝕎·) (k : ℕ) → #hasValue (#NUM k) w
#hasValue-N w k = lift (NUM k , tt , 0 , refl)

𝐕≡ : (w : 𝕎·) (a b : CTerm) → Set(lsuc(L))
𝐕≡ w a b = #weakMonEq! w a b

𝐕≡-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a b : CTerm} → 𝐕≡ w1 a b → 𝐕≡ w2 a b
𝐕≡-mon {w1} {w2} e {a} {b} h = ∀𝕎-mon e h

∈𝐕 : (w : 𝕎·) (t : CTerm) → Set(lsuc(L))
∈𝐕 w t = 𝐕≡ w t t

□∈𝐕 : (w : 𝕎·) (t : CTerm) → Set(lsuc(L))
□∈𝐕 w t = □· w (λ w' _ → ∈𝐕 w' t)

∈𝟙→∈𝐕 : (i : ℕ) (w : 𝕎·) (a : CTerm)
      → ∈Type i w 𝟙 a
      → ∈Type i w 𝐕 a
∈𝟙→∈𝐕 i w a a∈ = equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 (h1 , h2) → h1) (equalInTypeSUBSING→ a∈))

equalInType-N0→ : (i : ℕ) (w : 𝕎·) (a : CTerm)
                → equalInType i w 𝟙 a 𝕦
                → ∈Type i w 𝐕 a
equalInType-N0→ i w a h = ∈𝟙→∈𝐕 i w a (equalInType-refl h)

→equalInType-N0 : (i : ℕ) (w : 𝕎·) (a : CTerm)
                → ∈Type i w 𝐕 a
                → equalInType i w 𝟙 a 𝕦
→equalInType-N0 i w a h =
  →equalInTypeSUBSING eqTypesQNAT! (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalInType i w' 𝐕) a 𝕦)
  aw w1 e1  = equalInType-mon h w1 e1 , NUM-equalInType-QNAT! i w1 0

→∈Type-N : (i : ℕ) (w : 𝕎·) (k : ℕ)
         → ∈Type i w 𝟙 (#NUM k)
→∈Type-N i w k =
  →equalInTypeSUBSING eqTypesQNAT! (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalInType i w' 𝐕) (#NUM k) (#NUM k))
  aw w1 e1  = NUM-equalInType-QNAT! i w1 k , NUM-equalInType-QNAT! i w1 k

isNat→hasValue : (w : 𝕎·) (t : CTerm)
               → ∈𝐕 w t
               → #hasValue t w
isNat→hasValue w t h with h w (⊑-refl· w)
... | lift (n , c₁ , c₂) = lift (NUM n , tt , ⇓!→⇓ {w} {⌜ t ⌝} {NUM n} c₁)

isNat→∈Nat : (i : ℕ) (w : 𝕎·) (t : CTerm)
           → ∈𝐕 w t
           → ∈Type i w 𝐕 t
isNat→∈Nat i w t h = →equalInType-QNAT! i w t t (Mod.∀𝕎-□ M (λ w1 e1 → 𝐕≡-mon e1 {t} {t} h))

↓→ : (i : ℕ) (w : 𝕎·) (t : CTerm) → inhType i w (t ↓) → □∈𝐕 w t
↓→ i w t (a , j) = Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInTypePARTIAL→ (equalInType-EQ→₁ j)))
  where
  aw : ∀𝕎 w (λ w' e' → PARTIALeq (equalInType i w' 𝟙) w' t 𝕦
                     → □· w' (↑wPred' (λ w'' _ → ∈𝐕 w'' t) e'))
  aw w1 e1 h with h w1 (⊑-refl· w1)
  ... | h1 , h2 , h3 = Mod.∀𝕎-□Func M aw1 (equalInType-QNAT!→ i w1 t t h4)
    where
    h4 : ∈Type i w1 𝐕 t
    h4 = equalInType-N0→ i w1 t (h3 (h2 (#hasValue-N0 w1)))

    aw1 : ∀𝕎 w1  (λ w' e' → 𝐕≡ w' t t
                          → ↑wPred' (λ w'' _ → ∈𝐕 w'' t) e1 w' e')
    aw1 w2 e2 h z = h

→↓ : (i : ℕ) (w : 𝕎·) (t : CTerm) → □∈𝐕 w t → inhType i w (t ↓)
→↓ i w t j = #AX , →equalInType-EQ (→equalInTypePARTIAL eqTypesN (Mod.∀𝕎-□Func M aw j))
  where
  aw : ∀𝕎 w (λ w' e' → ∈𝐕 w' t → PARTIALeq (equalInType i w' 𝟙) w' t 𝕦)
  aw w1 e1 h w2 e2 =
    (λ q → #hasValue-N0 w2) ,
    (λ q → isNat→hasValue w2 t (𝐕≡-mon e2 {t} {t} h)) ,
    (λ q → →equalInType-N0 i w1 t (isNat→∈Nat i w1 t h))

-- MOVE to utils
≤suc : (n : ℕ) → n ≤ suc n
≤suc 0 = _≤_.z≤n
≤suc (suc n) = _≤_.s≤s (≤suc n)

NUM∈𝐒 : (i : ℕ) (w : 𝕎·) (k : ℕ) → ∈Type i w 𝐒 (#NUM k)
NUM∈𝐒 i w k = →equalInTypePARTIAL eqTypesN (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' _ → PARTIALeq (equalInType i w' 𝟙) w' (#NUM k) (#NUM k))
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

-- ι is a function from 𝐒 to Uᵢ
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

-- forces the argument to be a number
is𝐕 : CTerm → CTerm
is𝐕 a = #SUC a

-- meet operation on elements of 𝐒
_⊓_ : CTerm → CTerm → CTerm
a ⊓ b = #SEQ (is𝐕 a) b

SEQ-val⇓from-to₁ : {w : 𝕎·} {t v : Term} → isValue v → # t → SEQ v t ⇓ t from w to w
SEQ-val⇓from-to₁ {w} {t} {v} isv #t = 1 , c0
  where
  c0 : steps 1 (SEQ v t , w) ≡ (t , w)
  c0 with isValue⊎ v
  ... | inj₁ x rewrite #shiftUp 0 (ct t #t) | subNotIn v t #t = refl
  ... | inj₂ x = ⊥-elim (x isv)

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

SUC∈𝕍 : (w : 𝕎·) (a : CTerm)
      → ∈𝐕 w a
      → ∈𝐕 w (#SUC a)
SUC∈𝕍 w a a∈ w1 e1 with a∈ w1 e1
... | lift (n , c₁ , c₂) = lift (suc n , ⇓NUM→SUC⇓NUM c₁ , ⇓NUM→SUC⇓NUM c₂)

SEQ∈𝐕 : (w : 𝕎·) (a b : CTerm)
      → ∈𝐕 w a
      → ∈𝐕 w b
      → ∈𝐕 w (#SEQ a b)
SEQ∈𝐕 w a b a∈ b∈ w1 e1 with a∈ w1 e1 | b∈ w1 e1
... | lift (n , c₁ , c₂) | lift (m , d₁ , d₂) =
  lift (m ,
        ⇓-trans₂ {w1} {w1} {w1} {⌜ #SEQ a b ⌝} {⌜ #SEQ (#NUM n) b ⌝} {NUM m}
          (SEQ⇓₁ {w1} {w1} {⌜ a ⌝} {NUM n} {⌜ b ⌝} c₁)
          (⇓-trans₂ {w1} {w1} {w1} {⌜ #SEQ (#NUM n) b ⌝} {⌜ b ⌝} {NUM m}
            (SEQ-val⇓from-to₁ {w1} {⌜ b ⌝} {NUM n} tt (CTerm.closed b))
            d₁) ,
        ⇓-trans₂ {w1} {w1} {w1} {⌜ #SEQ a b ⌝} {⌜ #SEQ (#NUM n) b ⌝} {NUM m}
          (SEQ⇓₁ {w1} {w1} {⌜ a ⌝} {NUM n} {⌜ b ⌝} c₁)
          (⇓-trans₂ {w1} {w1} {w1} {⌜ #SEQ (#NUM n) b ⌝} {⌜ b ⌝} {NUM m}
            (SEQ-val⇓from-to₁ {w1} {⌜ b ⌝} {NUM n} tt (CTerm.closed b))
            d₁))

SUC-steps→ : (k : ℕ) (a v : Term) (w w' : 𝕎·)
           → isValue v
           → steps k (SUC a , w) ≡ (v , w')
           → Σ ℕ (λ m → a ⇓ NUM m from w to w')
SUC-steps→ 0 a v w w' isv comp
  rewrite sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = ⊥-elim isv
SUC-steps→ (suc k) a v w w' isv comp with is-NUM a
... | inj₁ (m , p)
  rewrite p
        | stepsVal (NUM (suc m)) w k tt
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = m , 0 , refl
... | inj₂ y with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z with SUC-steps→ k a' v w'' w' isv comp
... |      j , c = j , step-⇓-from-to-trans {w} {w''} {w'} {a} {a'} {NUM j} z c
SUC-steps→ (suc k) a v w w' isv comp | inj₂ y | inj₂ z
  rewrite z
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = ⊥-elim isv

SUC→ : (a v : Term) (w w' : 𝕎·)
     → isValue v
     → SUC a ⇓ v from w to w'
     → Σ ℕ (λ m → a ⇓ NUM m from w to w')
SUC→  a v w w' isv (k , comp) = SUC-steps→ k a v w w' isv comp

LET→ : (a b v : Term) (w w' : 𝕎·)
     → isValue v
     → LET a b ⇓ v from w to w'
     → hasValue a w
LET→ a b v w w' isv (k , comp) with LET→hasValue k a b v w w' comp isv
... | v1 , w1 , c1 , isv1 = v1 , w1 , (k , c1) , isv1

↓⊓→ₗ𝟙 : (i : ℕ) (w : 𝕎·) (a b : CTerm)
      → ∈Type i w 𝐒 a
      → inhType i w ((a ⊓ b) ↓)
      → ∈Type i w 𝟙 a
↓⊓→ₗ𝟙 i w a b a∈ j =
  equalInType-local (∀𝕎-□Func2 aw (↓→ i w (a ⊓ b) j) (equalInTypePARTIAL→ a∈))
  where
  aw : ∀𝕎 w (λ w' e' → ∈𝐕 w' (a ⊓ b)
                     → PARTIALeq (equalInType i w' 𝟙) w' a a
                     → ∈Type i w' 𝟙 a)
  aw w1 e1 h q with h w1 (⊑-refl· w1) | q w1 (⊑-refl· w1)
  ... | lift (n , c₁ , c₂) | (q1 , q2 , q3) with LET→ ⌜ #SUC a ⌝ (shiftUp 0 ⌜ b ⌝) (NUM n) w1 w1 tt c₁
  ... | u , w0 , c1 , isv1 with SUC→ ⌜ a ⌝ u w1 w0 isv1 c1
  ... | m , z =
    q3 (lift (NUM m , tt , ⇓-from-to→⇓ {w1} {w0} {⌜ a ⌝} {NUM m} z))

↓⊓→ₗ𝐕 : (i : ℕ) (w : 𝕎·) (a b : CTerm)
      → ∈Type i w 𝐒 a
      → inhType i w ((a ⊓ b) ↓)
      → ∈Type i w 𝐕 a
↓⊓→ₗ𝐕 i w a b a∈ j = ∈𝟙→∈𝐕 i w a (↓⊓→ₗ𝟙 i w a b a∈ j)

SEQ-steps→ᵣ : (k l : ℕ) (a b v u : Term) (w w1 w2 : 𝕎·)
            → isValue v
            → isValue u
            → steps l (a , w) ≡ (u , w1)
            → steps k (SEQ a b , w) ≡ (v , w2)
            → b ⇓ v from w1 to w2
SEQ-steps→ᵣ 0 l a b v u w w1 w2 isv isu ca cs
  rewrite sym (pair-inj₁ cs)
        | sym (pair-inj₂ cs) = ⊥-elim isv
SEQ-steps→ᵣ (suc k) l a b v u w w1 w2 isv isu ca cs with isValue⊎ a
... | inj₁ x
  rewrite sub-shiftUp0≡ a b
        | stepsVal a w l x
        | sym (pair-inj₁ ca)
        | sym (pair-inj₂ ca) = k , cs
... | inj₂ x with step⊎ a w
SEQ-steps→ᵣ (suc k) 0 a b v u w w1 w2 isv isu ca cs | inj₂ x | inj₁ (a' , w'' , z)
  rewrite z
        | sym (pair-inj₁ ca)
        | sym (pair-inj₂ ca) = ⊥-elim (x isu)
SEQ-steps→ᵣ (suc k) (suc l) a b v u w w1 w2 isv isu ca cs | inj₂ x | inj₁ (a' , w'' , z)
  rewrite z = SEQ-steps→ᵣ k l a' b v u w'' w1 w2 isv isu ca cs
SEQ-steps→ᵣ (suc k) l a b v u w w1 w2 isv isu ca cs | inj₂ x | inj₂ z
  rewrite z
        | sym (pair-inj₁ cs)
        | sym (pair-inj₂ cs) = ⊥-elim isv

SEQ→ᵣ : (a b v u : Term) (w w1 w2 : 𝕎·)
      → isValue v
      → isValue u
      → a ⇓ u from w to w1
      → SEQ a b ⇓ v from w to w2
      → b ⇓ v from w1 to w2
SEQ→ᵣ a b v u w w1 w2 isv isu (l , ca) (k , cs) = SEQ-steps→ᵣ k l a b v u w w1 w2 isv isu ca cs

↓⊓→ᵣ𝐕 : (i : ℕ) (w : 𝕎·) (a b : CTerm)
      → ∈Type i w 𝐒 a
      → inhType i w ((a ⊓ b) ↓)
      → ∈Type i w 𝐕 b
↓⊓→ᵣ𝐕 i w a b a∈ j =
  →equalInType-QNAT! i w b b (∀𝕎-□Func2 aw (↓→ i w (a ⊓ b) j) (equalInType-QNAT!→ i w a a (↓⊓→ₗ𝐕 i w a b a∈ j)))
  where
  aw : ∀𝕎 w (λ w' e' → ∈𝐕 w' (a ⊓ b) → ∈𝐕 w' a → ∈𝐕 w' b)
  aw w1 e1 h q w2 e2 with h w2 e2 | q w2 e2
  ... | lift (n , c₁ , c₂) | lift (m , d₁ , d₂) =
    lift (n ,
          SEQ→ᵣ ⌜ #SUC a ⌝ ⌜ b ⌝ (NUM n) (NUM (suc m)) w2 w2 w2 tt tt (⇓NUM→SUC⇓NUM d₁) c₁ ,
          SEQ→ᵣ ⌜ #SUC a ⌝ ⌜ b ⌝ (NUM n) (NUM (suc m)) w2 w2 w2 tt tt (⇓NUM→SUC⇓NUM d₁) c₁)

-- If a and b converge then (a ⊓ b) converges
→↓⊓ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
    → inhType i w (a ↓)
    → inhType i w (b ↓)
    → inhType i w ((a ⊓ b) ↓)
→↓⊓ i w a b ca cb =
  →↓ i w (a ⊓ b) (∀𝕎-□Func2 aw (Mod.∀𝕎-□Func M (λ w1 e1 z → SUC∈𝕍 w1 a z) (↓→ i w a ca)) (↓→ i w b cb))
  where
  aw : ∀𝕎 w (λ w' e' → ∈𝐕 w' (#SUC a) → ∈𝐕 w' b → ∈𝐕 w' (a ⊓ b))
  aw w1 e1 h q = SEQ∈𝐕 w1 (#SUC a) b h q

-- If (a ⊓ b) converges then a converges
↓⊓→ₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
     → ∈Type i w 𝐒 a
     → inhType i w ((a ⊓ b) ↓)
     → inhType i w (a ↓)
↓⊓→ₗ i w a b a∈ j = →↓ i w a (equalInType-QNAT!→ i w a a (↓⊓→ₗ𝐕 i w a b a∈ j))

-- If (a ⊓ b) converges then b converges
↓⊓→ᵣ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
     → ∈Type i w 𝐒 a
     → inhType i w ((a ⊓ b) ↓)
     → inhType i w (b ↓)
↓⊓→ᵣ i w a b a∈ j = →↓ i w b (equalInType-QNAT!→ i w b b (↓⊓→ᵣ𝐕 i w a b a∈ j))

□inhType : (i : ℕ) → INHT
□inhType i w T = □· w (λ w' _ → inhType i w' T)

-- λ t : 𝕌ᵢ → Σ (s : 𝐒). s ↓ ≡ t ∈ 𝕌ᵢ
∈𝐒 : ℕ → CTerm → CTerm
∈𝐒 i t = #SUM 𝐒 (#[0]EQ (#[0]VAR ↓₀) ⌞ t ⌟ ⌞ #UNIV i ⌟)

∈Type𝐒 : (i : ℕ) (w : 𝕎·) (t : CTerm) → Set(lsuc L)
∈Type𝐒 i w t = □inhType (suc i) w (∈𝐒 i t)

-- (u ∈ 𝐒) (q : Ω) → (ι(u) → p ∈ₛ 𝕊) → ι(u) ∧ p ∈ₛ 𝐒
-- where p ∈ₛ 𝐒 :≡ Σ (s : 𝐒). ι(s) = p ∈ Set
dom : (i : ℕ) (w : 𝕎·) (u p : CTerm)
    → ∈Type i w 𝐒 u
    → isType i w p
    → ∀𝕎 w (λ w' _ → □inhType i w' (u ↓) → ∈Type𝐒 i w p)
    → ∈Type𝐒 i w (#PROD (u ↓) p)
dom i w u p u∈ p∈ f =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInTypePARTIAL→ u∈))
  where
  aw : ∀𝕎 w (λ w' e' → PARTIALeq (equalInType i w' 𝟙) w' u u
                     → □· w' (↑wPred' (λ w'' _ → inhType (suc i) w'' (∈𝐒 i (#PROD (u ↓) p))) e'))
  aw w1 e1 h with EM {#hasValue u w1}
  ... | yes q = {!!} -- use classical logic to check whether (#hasValue u w1)
  ... | no q = {!!} -- use classical logic to check whether (#hasValue u w1)

\end{code}
