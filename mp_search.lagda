\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
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
open import progress
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import mod
open import encode


module mp_search {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice)
                 (K : Compatible W C)
                 (G : GetChoice {L} W C K)
                 (X : ChoiceExt {L} W C)
                 (N : NewChoice {L} W C K G)
                 (EC : Encode)
       where


open import worldDef(W)
open import choiceDef{L}(C)
--open import compatibleDef{L}(W)(C)(K)
--open import getChoiceDef(W)(C)(K)(G)
--open import newChoiceDef(W)(C)(K)(G)(N)
--open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
--open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
--open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
open import props4(W)(M)(C)(K)(G)(X)(N)(EC)

open import props6(W)(M)(C)(K)(G)(X)(N)(EC)
  using (SUMeq! ; equalInType-SUM! ; equalInType-SUM!→)

open import type_sys_props_isect(W)(M)(C)(K)(G)(X)(N)(EC)

open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#MP-right ; #MP-right2 ; isType-MP-right-body)


-- MOVE
#⇛!-mon : {a b : CTerm} {w2 w1 : 𝕎·}
        → w1 ⊑· w2
        → a #⇛! b at w1
        → a #⇛! b at w2
#⇛!-mon {a} {b} {w2} {w1} ext c w' e' = c w' (⊑-trans· ext e')


infSearchI : Term → Term → Term → Term
infSearchI f R n =
  ITE (APPLY f n)
      n
      (LET (SUC n) (APPLY (shiftUp 0 R) (VAR 0)))


-- This is the body of the fix in infSearch
infSearchL : Term → Term
infSearchL f =
  -- 1 is the recursive call and 0 is the number
  LAMBDA (LAMBDA (infSearchI (shiftUp 0 (shiftUp 0 f)) (VAR 1) (VAR 0)))


infSearchF : Term → Term
infSearchF f = FIX (infSearchL f)


-- f is a function in #NAT!→BOOL
-- We're defining here the infinite search: fix(λR.λn.if f(n) then n else R(suc(n)))0
-- The closed version #infSearch is below
infSearch : Term → Term
infSearch f = APPLY (infSearchF f) N0


#infSearchI : CTerm → CTerm → CTerm → CTerm
#infSearchI f R n =
  #ITE (#APPLY f n)
       n
       (#LET (#SUC n) (#[0]APPLY (#[0]shiftUp0 R) #[0]VAR))


-- The body of #infSearch fix's body
#infSearchL : CTerm → CTerm
#infSearchL f =
  #LAMBDA (#[0]LAMBDA (#[1]ITE (#[1]APPLY (#[1]shiftUp0 (#[0]shiftUp0 f)) (#[1]VAR0))
                               (#[1]VAR0)
                               (#[1]LET (#[1]SUC #[1]VAR0) (#[2]APPLY #[2]VAR2 (#[2]VAR0)))))


#infSearchF : CTerm → CTerm
#infSearchF f = #FIX (#infSearchL f)


#infSearch : CTerm → CTerm
#infSearch f = #APPLY (#infSearchF f) #N0


#infSearchP : CTerm → CTerm
#infSearchP f = #PAIR (#infSearch f) #AX


-- sanity check
⌜#infSearch⌝ : (f : CTerm) → ⌜ #infSearch f ⌝ ≡ infSearch ⌜ f ⌝
⌜#infSearch⌝ f = refl


∈#BOOL₀→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
            → equalInType i w #BOOL₀ a b
            → □· w (λ w' _ → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' a b)
∈#BOOL₀→ u w a b b∈ = eqInType-⇛-BOOL₀ u w a b (fst b∈) (snd b∈)


#⇛!sameℕ-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a b : CTerm}
                 → #⇛!sameℕ w1 a b
                 → #⇛!sameℕ w2 a b
#⇛!sameℕ-mon {w1} {w2} e {a} {b} (n , c₁ , c₂) = n , ∀𝕎-mon e c₁ , ∀𝕎-mon e c₂


∈#NAT!→BOOL₀→ : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                 → equalInType i w #NAT!→BOOL₀ f₁ f₂
                 → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → #⇛!sameℕ w' n₁ n₂
                                → □· w' (λ w' e → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ n₁) (#APPLY f₂ n₂)))
∈#NAT!→BOOL₀→ i w f₁ f₂ f∈ w1 e1 n₁ n₂ n∈ =
  ∈#BOOL₀→
    i w1 (#APPLY f₁ n₁) (#APPLY f₂ n₂)
    (equalInType-FUN→
       (≡CTerm→equalInType #NAT!→BOOL₀≡ f∈) w1 e1 n₁ n₂
       (→equalInType-NAT! i w1 n₁ n₂ (Mod.∀𝕎-□ M λ w2 e2 → #⇛!sameℕ-mon e2 {n₁} {n₂} n∈)))


∈#NAT!→BOOL₀≤→ : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm) (n : ℕ)
                   → equalInType i w #NAT!→BOOL₀ f₁ f₂
                   → □· w (λ w' e → (m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
∈#NAT!→BOOL₀≤→ i w f₁ f₂ 0 f∈ = Mod.∀𝕎-□Func M aw c
  where
    c : □· w (λ w' e → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ #N0) (#APPLY f₂ #N0))
    c = ∈#NAT!→BOOL₀→ i w f₁ f₂ f∈ w (⊑-refl· w) #N0 #N0 (#⇛!sameℕ-NUM w 0)

    aw : ∀𝕎 w (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ #N0) (#APPLY f₂ #N0)
                       → (m : ℕ) → m ≤ 0 → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
    aw w1 e1 h .ℕ.zero _≤_.z≤n = h
∈#NAT!→BOOL₀≤→ i w f₁ f₂ (suc n) f∈ = ∀𝕎-□Func2 aw c ind
  where
    ind : □· w (λ w' e → (m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
    ind = ∈#NAT!→BOOL₀≤→ i w f₁ f₂ n f∈

    c : □· w (λ w' e → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM (suc n))) (#APPLY f₂ (#NUM (suc n))))
    c = ∈#NAT!→BOOL₀→ i w f₁ f₂ f∈ w (⊑-refl· w) (#NUM (suc n)) (#NUM (suc n)) (#⇛!sameℕ-NUM w (suc n))

    aw : ∀𝕎 w (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM (suc n))) (#APPLY f₂ (#NUM (suc n)))
                       → ((m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                       → (m : ℕ) → m ≤ suc n → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
    aw w1 e1 h1 h2 m len with ≤suc→⊎ len
    ... | inj₁ p rewrite p = h1
    ... | inj₂ p = h2 m p


∈#ASSERT₂→ : (i : ℕ) (w : 𝕎·) (t a b : CTerm)
               → equalInType i w (#ASSERT₂ t) a b
               → □· w (λ w' _ → Σ CTerm (λ u → t #⇛ #INL u at w'))
∈#ASSERT₂→ i w t a b a∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₂≡ t) a∈)))
  where
    aw1 : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType i w' #BOOL₀) w' a b
                         → Mod.□ M w' (↑wPred' (λ w'' _ → Σ CTerm (λ u → t #⇛ #INL u at w'')) e'))
    aw1 w1 e1 h = Mod.∀𝕎-□Func M aw2 (∈#BOOL₀→ i w1 t #BTRUE h)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' t #BTRUE
                             → ↑wPred' (λ w'' _ → Σ CTerm (λ u → t #⇛ #INL u at w'')) e1 w' e')
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , q)) z = x , c₁
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , q)) z = ⊥-elim (INLneqINR (≡CTerm (#compAllVal {#BTRUE} {#INR y} {w2} c₂ tt)))


∈#ASSERT₂→2 : (i : ℕ) (w : 𝕎·) (f k a b : CTerm) (n : ℕ)
                → ∈Type i w #NAT!→BOOL₀ f
                → equalInType i w (#ASSERT₂ (#APPLY f k)) a b
                → k #⇛! #NUM n at w
                → □· w (λ w' _ → Σ CTerm (λ u → #APPLY f (#NUM n) #⇛ #INL u at w'))
∈#ASSERT₂→2 i w f k a b n f∈ a∈ ck =
  ∀𝕎-□Func2 aw h1 h2
  where
    h1 : □· w (λ w' e → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f k) (#APPLY f (#NUM n)))
    h1 = ∈#NAT!→BOOL₀→ i w f f f∈ w (⊑-refl· w) k (#NUM n) (n , ck , #⇛!-refl {w} {#NUM n})

    h2 : □· w (λ w' _ → Σ CTerm (λ u → #APPLY f k #⇛ #INL u at w'))
    h2 = ∈#ASSERT₂→ i w (#APPLY f k) a b a∈

    aw : ∀𝕎 w (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f k) (#APPLY f (#NUM n))
                       → (Σ CTerm (λ u → #APPLY f k #⇛ #INL u at w'))
                       → Σ CTerm (λ u → #APPLY f (#NUM n) #⇛ #INL u at w'))
    aw w1 e1 (x , y , inj₁ (c₁ , c₂ , q)) (u , d) = y , c₂
    aw w1 e1 (x , y , inj₂ (c₁ , c₂ , q)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛-val-det {w1} {#APPLY f k} {#INL u} {#INR x} tt tt d c₁)))


∈#ASSERT₂→3 : (i : ℕ) (w : 𝕎·) (f₁ f₂ k a b : CTerm) (n : ℕ)
                → equalInType i w #NAT!→BOOL₀ f₁ f₂
                → equalInType i w (#ASSERT₂ (#APPLY f₁ k)) a b
                → k #⇛! #NUM n at w
                → □· w (λ w' _ → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ →
                     #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w' ×  #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w')))
∈#ASSERT₂→3 i w f₁ f₂ k a b n f∈ a∈ ck =
  ∀𝕎-□Func3 aw h1 h2 h3
  where
    h1 : □· w (λ w' e → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ k) (#APPLY f₂ (#NUM n)))
    h1 = ∈#NAT!→BOOL₀→ i w f₁ f₂ f∈ w (⊑-refl· w) k (#NUM n) (n , ck , #⇛!-refl {w} {#NUM n})

    h2 : □· w (λ w' e → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM n)) (#APPLY f₂ (#NUM n)))
    h2 = ∈#NAT!→BOOL₀→ i w f₁ f₂ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (n , #⇛!-refl {w} {#NUM n} , #⇛!-refl {w} {#NUM n})

    h3 : □· w (λ w' _ → Σ CTerm (λ u → #APPLY f₁ k #⇛ #INL u at w'))
    h3 = ∈#ASSERT₂→ i w (#APPLY f₁ k) a b a∈

    aw : ∀𝕎 w (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ k) (#APPLY f₂ (#NUM n))
                       → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM n)) (#APPLY f₂ (#NUM n))
                       → (Σ CTerm (λ u → #APPLY f₁ k #⇛ #INL u at w'))
                       → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ →
                           #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w' × #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w')))
    aw w1 e1 (x₁ , x₂ , inj₁ (c₁ , c₂ , q)) (y₁ , y₂ , inj₁ (d₁ , d₂ , h)) (u , d) = y₁ , y₂ , d₁ , d₂
    aw w1 e1 (x₁ , x₂ , inj₁ (c₁ , c₂ , q)) (y₁ , y₂ , inj₂ (d₁ , d₂ , h)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛-val-det {w1} {#APPLY f₂ (#NUM n)} {#INL x₂} {#INR y₂} tt tt c₂ d₂)))
    aw w1 e1 (x₁ , x₂ , inj₂ (c₁ , c₂ , q)) (y₁ , y₂ , inj₁ (d₁ , d₂ , h)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛-val-det {w1} {#APPLY f₂ (#NUM n)} {#INL y₂} {#INR x₂} tt tt d₂ c₂)))
    aw w1 e1 (x₁ , x₂ , inj₂ (c₁ , c₂ , q)) (y₁ , y₂ , inj₂ (d₁ , d₂ , h)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛-val-det {w1} {#APPLY f₁ k} {#INL u} {#INR x₁} tt tt d c₁)))


≡→⇓from-to : {a b : Term} (w : 𝕎·) → a ≡ b → a ⇓ b from w to w
≡→⇓from-to {a} {b} w e rewrite e = 0 , refl


sub-LAMBDA-infSearchI : (f : Term) (#f : # f)
                        → sub (infSearchF f) (LAMBDA (infSearchI (shiftUp 0 (shiftUp 0 f)) (VAR 1) (VAR 0)))
                           ≡ LAMBDA (infSearchI f (infSearchF f) (VAR 0))
sub-LAMBDA-infSearchI f #f
  rewrite #shiftUp 0 (ct f #f)
        | #shiftUp 0 (ct f #f)
        | #shiftUp 2 (ct f #f)
        | #shiftUp 2 (ct f #f)
        | #shiftUp 2 (ct f #f)
        | #shiftUp 2 (ct f #f)
        | #shiftUp 3 (ct f #f)
        | #shiftUp 5 (ct f #f)
        | #subv 1 (FIX (LAMBDA (LAMBDA (DECIDE (APPLY f (VAR 0)) (VAR 1) (LET (SUC (VAR 1)) (APPLY (VAR 3) (VAR 0))))))) f #f
        | #shiftDown 1 (ct f #f)
        | #shiftDown 5 (ct f #f)
  = refl


sub-infSearchI : (f : Term) (#f : # f) (n : ℕ)
                 → sub (NUM n) (infSearchI f (infSearchF f) (VAR 0))
                    ≡ infSearchI f (infSearchF f) (NUM n)
sub-infSearchI f #f n
  rewrite #shiftUp 0 (ct f #f)
        | #shiftUp 0 (ct f #f)
        | #shiftUp 2 (ct f #f)
        | #shiftUp 3 (ct f #f)
        | #subv 0 (NUM n) f #f
        | #subv 4 (NUM n) f #f
        | #shiftDown 0 (ct f #f)
        | #shiftDown 4 (ct f #f)
  = refl


infSearch⇓₁ : (w : 𝕎·) (f : Term) (#f : # f) (n : ℕ)
              → APPLY (infSearchF f) (NUM n) ⇓ infSearchI f (infSearchF f) (NUM n) from w to w
infSearch⇓₁ w f #f n =
  step-⇓-from-to-trans
    {w} {w} {w}
    {APPLY (infSearchF f) (NUM n)}
    {APPLY (sub (infSearchF f) (LAMBDA (infSearchI (shiftUp 0 (shiftUp 0 f)) (VAR 1) (VAR 0)))) (NUM n)}
    {infSearchI f (infSearchF f) (NUM n)}
    refl
    (⇓-trans₂
      {w} {w} {w}
      {APPLY (sub (infSearchF f) (LAMBDA (infSearchI (shiftUp 0 (shiftUp 0 f)) (VAR 1) (VAR 0)))) (NUM n)}
      {APPLY (LAMBDA (infSearchI f (infSearchF f) (VAR 0))) (NUM n)}
      {infSearchI f (infSearchF f) (NUM n)}
      (≡→⇓from-to w (≡APPLY (sub-LAMBDA-infSearchI f #f) refl))
      (step-⇓-from-to-trans
        {w} {w} {w}
        {APPLY (LAMBDA (infSearchI f (infSearchF f) (VAR 0))) (NUM n)}
        {sub (NUM n) (infSearchI f (infSearchF f) (VAR 0))}
        {infSearchI f (infSearchF f) (NUM n)}
        refl
        (≡→⇓from-to w (sub-infSearchI f #f n))))


#infSearch⇛₁ : (w : 𝕎·) (f : CTerm) (n : ℕ)
                → #APPLY (#infSearchF f) (#NUM n) #⇛ #infSearchI f (#infSearchF f) (#NUM n) at w
#infSearch⇛₁ w f n w1 e1 = lift (⇓-from-to→⇓ (infSearch⇓₁ w1 ⌜ f ⌝ (CTerm.closed f) n))


#infSearch⇓₂ : (w1 w2 : 𝕎·) (f u R : Term) (n : ℕ)
                → APPLY f (NUM n) ⇓ INL u from w1 to w2
                → infSearchI f R (NUM n) ⇓ NUM n from w1 to w2
#infSearch⇓₂ w1 w2 f u R n comp =
  ⇓-trans₂
    {w1} {w2} {w2}
    {infSearchI f R (NUM n)}
    {ITE (INL u) (NUM n) (LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0)))}
    {NUM n}
    (ITE⇓₁ {w1} {w2} {APPLY f (NUM n)} {INL u} {NUM n} {LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0))} comp)
    (1 , refl)


#infSearch⇛₂ : (w : 𝕎·) (f u R : CTerm) (n : ℕ)
                → #APPLY f (#NUM n) #⇛ #INL u at w
                → #infSearchI f R (#NUM n) #⇛ #NUM n at w
#infSearch⇛₂ w f u R n comp w1 e1 =
  lift (⇓-from-to→⇓ (#infSearch⇓₂ w1 (fst c) ⌜ f ⌝ ⌜ u ⌝ ⌜ R ⌝ n (snd c)))
  where
    c : Σ 𝕎· (λ w' → #APPLY f (#NUM n) #⇓ #INL u from w1 to w')
    c = ⇛→⇓from-to (∀𝕎-mon e1 comp)


ITE-INR⇓ : (w : 𝕎·) (a t u : Term)
            → ITE (INR a) t u ⇓ u from w to w
ITE-INR⇓ w a t u = 1 , ≡pair (sub-shiftUp0≡ a u) refl


sub-APPLY-shiftUp0-VAR0 : (n : ℕ) (R : Term) (#R : # R)
                          → sub (NUM n) (APPLY (shiftUp 0 R) (VAR 0))
                             ≡ APPLY R (NUM n)
sub-APPLY-shiftUp0-VAR0 n R #R
  rewrite #shiftUp 0 (ct R #R)
        | #subv 0 (NUM n) R #R
        | #shiftDown 0 (ct R #R)
   = refl


#infSearch⇓₃ : (w1 w2 : 𝕎·) (f u R : Term) (n : ℕ) (#R : # R)
                → APPLY f (NUM n) ⇓ INR u from w1 to w2
                → infSearchI f R (NUM n) ⇓ APPLY R (NUM (suc n)) from w1 to w2
#infSearch⇓₃ w1 w2 f u R n #R comp =
  ⇓-trans₂
    {w1} {w2} {w2}
    {infSearchI f R (NUM n)}
    {ITE (INR u) (NUM n) (LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0)))}
    {APPLY R (NUM (suc n))}
    (ITE⇓₁ {w1} {w2} {APPLY f (NUM n)} {INR u} {NUM n} {LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0))} comp)
    (⇓-trans₂
      {w2} {w2} {w2}
      {ITE (INR u) (NUM n) (LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0)))}
      {LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0))}
      {APPLY R (NUM (suc n))}
      (ITE-INR⇓ w2 u (NUM n) (LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0))))
      (⇓-trans₂
        {w2} {w2} {w2}
        {LET (SUC (NUM n)) (APPLY (shiftUp 0 R) (VAR 0))}
        {LET (NUM (suc n)) (APPLY (shiftUp 0 R) (VAR 0))}
        {APPLY R (NUM (suc n))}
        (LET⇓ {SUC (NUM n)} {NUM (suc n)} (APPLY (shiftUp 0 R) (VAR 0)) {w2} {w2} (1 , refl))
        (⇓-trans₂
          {w2} {w2} {w2}
          {LET (NUM (suc n)) (APPLY (shiftUp 0 R) (VAR 0))}
          {sub (NUM (suc n)) (APPLY (shiftUp 0 R) (VAR 0))}
          {APPLY R (NUM (suc n))}
          (LET-val⇓ w2 (NUM (suc n)) (APPLY (shiftUp 0 R) (VAR 0)) tt)
          (≡→⇓from-to w2 (sub-APPLY-shiftUp0-VAR0 (suc n) R #R)))))


#infSearch⇛₃ : (w : 𝕎·) (f u R : CTerm) (n : ℕ)
                → #APPLY f (#NUM n) #⇛ #INR u at w
                → #infSearchI f R (#NUM n) #⇛ #APPLY R (#NUM (suc n)) at w
#infSearch⇛₃ w f u R n comp w1 e1 =
  lift (⇓-from-to→⇓ (#infSearch⇓₃ w1 (fst c) ⌜ f ⌝ ⌜ u ⌝ ⌜ R ⌝ n (CTerm.closed R) (snd c)))
  where
    c : Σ 𝕎· (λ w' → #APPLY f (#NUM n) #⇓ #INR u from w1 to w')
    c = ⇛→⇓from-to (∀𝕎-mon e1 comp)


-- by induction on j
mpSearch3 : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ : CTerm) (n k j : ℕ)
            → k + j ≡ n
            → ((m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w #TRUE) (equalInType i w #TRUE) w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
            → #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w
            → #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w
            → Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
                × #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM m at w
                × #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM m at w
                × #APPLY f₁ (#NUM m) #⇛ #INL u₁ at w
                × #APPLY f₂ (#NUM m) #⇛ #INL u₂ at w)))
mpSearch3 i w f₁ f₂ u₁ u₂ n k 0 eqn hn ha₁ ha₂ rewrite +0 k | eqn =
  n , u₁ , u₂ , ≤-refl ,
  #⇛-trans
    {w} {#APPLY (#infSearchF f₁) (#NUM n)} {#infSearchI f₁ (#infSearchF f₁) (#NUM n)} {#NUM n}
    (#infSearch⇛₁ w f₁ n)
    (#infSearch⇛₂ w f₁ u₁ (#infSearchF f₁) n ha₁) ,
  #⇛-trans
    {w} {#APPLY (#infSearchF f₂) (#NUM n)} {#infSearchI f₂ (#infSearchF f₂) (#NUM n)} {#NUM n}
    (#infSearch⇛₁ w f₂ n)
    (#infSearch⇛₂ w f₂ u₂ (#infSearchF f₂) n ha₂) ,
  ha₁ ,
  ha₂
mpSearch3 i w f₁ f₂ u₁ u₂ n k (suc j) eqn hn ha₁ ha₂ with hn k (+≡→≤ k (suc j) n eqn)
... | a₁ , a₂ , inj₁ (c₁ , c₂ , q) = concl
  where
    comp₁ : #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM k at w
    comp₁ = #⇛-trans
             {w} {#APPLY (#infSearchF f₁) (#NUM k)} {#infSearchI f₁ (#infSearchF f₁) (#NUM k)} {#NUM k}
             (#infSearch⇛₁ w f₁ k)
             (#infSearch⇛₂ w f₁ a₁ (#infSearchF f₁) k c₁)

    comp₂ : #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM k at w
    comp₂ = #⇛-trans
             {w} {#APPLY (#infSearchF f₂) (#NUM k)} {#infSearchI f₂ (#infSearchF f₂) (#NUM k)} {#NUM k}
             (#infSearch⇛₁ w f₂ k)
             (#infSearch⇛₂ w f₂ a₂ (#infSearchF f₂) k c₂)

    concl : Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
              × #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM m at w
              × #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM m at w
              × #APPLY f₁ (#NUM m) #⇛ #INL u₁ at w
              × #APPLY f₂ (#NUM m) #⇛ #INL u₂ at w)))
    concl = k , a₁ , a₂ , +≡→≤ k (suc j) n eqn , comp₁ , comp₂ , c₁ , c₂
... | a₁ , a₂ , inj₂ (c₁ , c₂ , q) = concl
  where
    comp₁ : #APPLY (#infSearchF f₁) (#NUM k) #⇛ #APPLY (#infSearchF f₁) (#NUM (suc k)) at w
    comp₁ = #⇛-trans
             {w} {#APPLY (#infSearchF f₁) (#NUM k)} {#infSearchI f₁ (#infSearchF f₁) (#NUM k)} {#APPLY (#infSearchF f₁) (#NUM (suc k))}
             (#infSearch⇛₁ w f₁ k)
             (#infSearch⇛₃ w f₁ a₁ (#infSearchF f₁) k c₁)

    comp₂ : #APPLY (#infSearchF f₂) (#NUM k) #⇛ #APPLY (#infSearchF f₂) (#NUM (suc k)) at w
    comp₂ = #⇛-trans
             {w} {#APPLY (#infSearchF f₂) (#NUM k)} {#infSearchI f₂ (#infSearchF f₂) (#NUM k)} {#APPLY (#infSearchF f₂) (#NUM (suc k))}
             (#infSearch⇛₁ w f₂ k)
             (#infSearch⇛₃ w f₂ a₂ (#infSearchF f₂) k c₂)

    ind : Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
            × #APPLY (#infSearchF f₁) (#NUM (suc k)) #⇛ #NUM m at w
            × #APPLY (#infSearchF f₂) (#NUM (suc k)) #⇛ #NUM m at w
            × #APPLY f₁ (#NUM m) #⇛ #INL u₁ at w
            × #APPLY f₂ (#NUM m) #⇛ #INL u₂ at w)))
    ind = mpSearch3 i w f₁ f₂ u₁ u₂ n (suc k) j (trans (sym (+-suc k j)) eqn) hn ha₁ ha₂

    concl : Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
              × #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM m at w
              × #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM m at w
              × #APPLY f₁ (#NUM m) #⇛ #INL u₁ at w
              × #APPLY f₂ (#NUM m) #⇛ #INL u₂ at w)))
    concl = fst ind , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
            #⇛-trans {w} {#APPLY (#infSearchF f₁) (#NUM k)} {#APPLY (#infSearchF f₁) (#NUM (suc k))} {#NUM (fst ind)} comp₁ (fst (snd (snd (snd (snd ind))))) ,
            #⇛-trans {w} {#APPLY (#infSearchF f₂) (#NUM k)} {#APPLY (#infSearchF f₂) (#NUM (suc k))} {#NUM (fst ind)} comp₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
            fst (snd (snd (snd (snd (snd (snd ind)))))) ,
            snd (snd (snd (snd (snd (snd (snd ind))))))


mpSearch2 : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ : CTerm) (n : ℕ)
            → ((m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w #TRUE) (equalInType i w #TRUE) w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
            → #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w
            → #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w
            → Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
                  × #infSearch f₁ #⇛ #NUM m at w
                  × #infSearch f₂ #⇛ #NUM m at w
                  × #APPLY f₁ (#NUM m) #⇛ #INL u₁ at w
                  × #APPLY f₂ (#NUM m) #⇛ #INL u₂ at w)))
mpSearch2 i w f₁ f₂ u₁ u₂ n hn ha₁ ha₂ = mpSearch3 i w f₁ f₂ u₁ u₂ n 0 n refl hn ha₁ ha₂


#¬Names→⇛! : (w : 𝕎·) (t u : CTerm)
               → #¬Names t
               → t #⇛ u at w
               → t #⇛! u at w
#¬Names→⇛! w t u nnt comp w1 e1 = lift (¬Names→⇓from-to w1 w1 ⌜ t ⌝ ⌜ u ⌝ nnt (lower (comp w1 e1)))


#¬Names-#infSearch : {f : CTerm}
                     → #¬Names f
                     → #¬Names (#infSearch f)
#¬Names-#infSearch {f} nnf
  rewrite #shiftUp 0 f
        | #shiftUp 0 f
        | nnf = refl


mpSearch2¬Names : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ : CTerm) (n : ℕ)
                  → #¬Names f₁
                  → #¬Names f₂
                  → ((m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w #TRUE) (equalInType i w #TRUE) w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                  → #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w
                  → #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w
                  → Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
                      × #infSearch f₁ #⇛! #NUM m at w
                      × #infSearch f₂ #⇛! #NUM m at w
                      × #APPLY f₁ (#NUM m) #⇛ #INL u₁ at w
                      × #APPLY f₂ (#NUM m) #⇛ #INL u₂ at w)))
mpSearch2¬Names i w f₁ f₂ u₁ u₂ n nnf₁ nnf₂ hn ha₁ ha₂ with mpSearch2 i w f₁ f₂ u₁ u₂ n hn ha₁ ha₂
... | m , v₁ , v₂ , len , c₁ , c₂ , d₁ , d₂ = m , v₁ , v₂ , len , concl₁ , concl₂ , d₁ , d₂
  where
    concl₁ : #infSearch f₁ #⇛! #NUM m at w
    concl₁ = #¬Names→⇛! w (#infSearch f₁) (#NUM m) (#¬Names-#infSearch {f₁} nnf₁) c₁

    concl₂ : #infSearch f₂ #⇛! #NUM m at w
    concl₂ = #¬Names→⇛! w (#infSearch f₂) (#NUM m) (#¬Names-#infSearch {f₂} nnf₂) c₂


∈#NAT!→BOOL→equalInType-#ASSERT₂ : (i : ℕ) (w : 𝕎·) (f t u : CTerm) (m : ℕ)
                                     → ∈Type i w #NAT!→BOOL₀ f
                                     → t #⇛! #NUM m at w
                                     → #APPLY f (#NUM m) #⇛ #INL u at w
                                     → ∈Type i w (#ASSERT₂ (#APPLY f t)) #AX
∈#NAT!→BOOL→equalInType-#ASSERT₂ i w f t u m f∈ cm cl =
  ≡CTerm→equalInType
    (sym (#ASSERT₂≡ (#APPLY f t)))
    (equalInType-EQ
      isTypeBOOL₀
      (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w (λ w' _ → equalInType i w' #BOOL₀ (#APPLY f t) #BTRUE)
    aw w1 e1 =
      equalInType-trans eqb (strongBool→equalInType-BOOL₀ i w1 (#APPLY f (#NUM m)) (#BTRUE) (Mod.∀𝕎-□ M aw1))
      where
        aw1 : ∀𝕎 w1 (λ w' _ → #strongBool w' (#APPLY f (#NUM m)) #BTRUE)
        aw1 w2 e2 = u , #AX , inj₁ (∀𝕎-mon (⊑-trans· e1 e2) cl , #⇛-refl w2 #BTRUE)

        eqn : equalInType i w1 #NAT! t (#NUM m)
        eqn = →equalInType-NAT!
                i w1 t (#NUM m)
                (Mod.∀𝕎-□ M (λ w2 e2 → m , ∀𝕎-mon (⊑-trans· e1 e2) cm , #⇛!-refl {w2} {#NUM m}))

        eqb : equalInType i w1 #BOOL₀ (#APPLY f t) (#APPLY f (#NUM m))
        eqb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀≡ f∈) w1 e1 t (#NUM m) eqn


mpSearch1 : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ t₁ t₂ : CTerm) (n : ℕ)
            → equalInType i w #NAT!→BOOL₀ f₁ f₂
            → #¬Names f₁
            → #¬Names f₂
            → t₁ #⇛! #infSearchP f₁ at w
            → t₂ #⇛! #infSearchP f₂ at w
            → ((m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w #TRUE) (equalInType i w #TRUE) w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
            → #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w
            → #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w
            → SUMeq! (equalInType i w #NAT!) (λ a b ea → equalInType i w (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w t₁ t₂
mpSearch1 i w f₁ f₂ u₁ u₂ t₁ t₂ n f∈ nnf₁ nnf₂ ct₁ ct₂ hn ha₁ ha₂ with mpSearch2¬Names i w f₁ f₂ u₁ u₂ n nnf₁ nnf₂ hn ha₁ ha₂
... | m , v₁ , v₂ , len , c₁ , c₂ , d₁ , d₂ =
  #infSearch f₁ , #infSearch f₂ , #AX , #AX ,
  -- How can we prove that it lives in #NAT! if f is not pure? Could we use #NAT for the impure version of MP? Negation is fine though
  →equalInType-NAT! i w (#infSearch f₁) (#infSearch f₂) (Mod.∀𝕎-□ M p1) ,
  ct₁ , --lower (ct₁ w (⊑-refl· w)) , --ct₁ ,
  ct₂ , --lower (ct₂ w (⊑-refl· w)) , --ct₂ ,
  p2
-- For this we need to prove that (#infSearch f) computes to a number m ≤ n such that (#APPLY f (#NUM m)) computes to #INL
-- If f is not pure this might only be at a higher world, but if f is pure we can bring back the computation to the current world
-- ...so assume #¬Names f for this
  where
    p1 : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#infSearch f₁) (#infSearch f₂))
    p1 w1 e1 = m , ∀𝕎-mon e1 c₁ , ∀𝕎-mon e1 c₂

    p2 : ∈Type i w (sub0 (#infSearch f₁) (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR))) #AX
    p2 = ≡CTerm→equalInType
           (sym (sub0-ASSERT₂-APPLY (#infSearch f₁) f₁))
           (∈#NAT!→BOOL→equalInType-#ASSERT₂ i w f₁ (#infSearch f₁) v₁ m (equalInType-refl f∈) c₁ d₁)


mpSearch : (i : ℕ) (w : 𝕎·) (f₁ f₂ a₁ a₂ t₁ t₂ : CTerm)
           → #¬Names f₁
           → #¬Names f₂
           → t₁ #⇛! #infSearchP f₁ at w
           → t₂ #⇛! #infSearchP f₂ at w
           → equalInType i w #NAT!→BOOL₀ f₁ f₂
           → equalInType i w (#MP-right f₁) a₁ a₂
           → equalInType i w (#MP-right2 f₁) t₁ t₂
mpSearch i w f₁ f₂ a₁ a₂ t₁ t₂ nnf₁ nnf₂ ct₁ ct₂ f∈ a∈ =
  equalInType-local (Mod.∀𝕎-□Func M aw1 h1)
  where
    h1 : □· w (λ w' _ → inhType i w' (#MP-right2 f₁))
    h1 = equalInType-SQUASH→ a∈

    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2 f₁)
                         → equalInType i w' (#MP-right2 f₁) t₁ t₂)
    aw1 w1 e1 (t , t∈) =
      equalInType-local (Mod.∀𝕎-□Func M aw2 p∈)
      where
        p∈ : □· w1 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' t t)
        p∈ = equalInType-SUM!→ {B = #[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)} t∈

        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' t t
                             → equalInType i w' (#MP-right2 f₁) t₁ t₂)
        aw2 w2 e2 (n₁ , n₂ , x₁ , x₂ , n∈ , c₁ , c₂ , x∈) =
          equalInType-local (Mod.∀𝕎-□Func M aw3 (equalInType-NAT!→ i w2 n₁ n₂ n∈))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                                  → equalInType i w' (#MP-right2 f₁) t₁ t₂)
            aw3 w3 e3 (n , d₁ , d₂) =
              equalInType-SUM!
                {B = #[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)}
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-body i w3 f₁ f₁ (equalInType-refl (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                (∀𝕎-□Func2 aw4 h2 y∈)
              where
                y∈ : □· w3 (λ w' _ → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ →
                                             #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w' × #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w')))
                y∈ = ∈#ASSERT₂→3 i w3 f₁ f₂ n₁ x₁ x₂ n (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f₁) (equalInType-mon x∈ w3 e3)) d₁

                h2 : □· w3 (λ w' e → (m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                h2 = ∈#NAT!→BOOL₀≤→ i w3 f₁ f₂ n (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3)))

                aw4 : ∀𝕎 w3 (λ w' e' → ((m : ℕ) → m ≤ n → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                                      → (Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → #APPLY f₁ (#NUM n) #⇛ #INL u₁ at w' × #APPLY f₂ (#NUM n) #⇛ #INL u₂ at w')))
                                      → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' t₁ t₂)
                aw4 w4 e4 hn (u₁ , u₂ , ha₁ , ha₂) =
                  mpSearch1
                    i w4 f₁ f₂ u₁ u₂ t₁ t₂ n
                    (equalInType-mon f∈ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))))
                    nnf₁ nnf₂
                    (#⇛!-mon {t₁} {#infSearchP f₁} (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) ct₁)
                    (#⇛!-mon {t₂} {#infSearchP f₂} (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) ct₂)
                    hn ha₁ ha₂

\end{code}
