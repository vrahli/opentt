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
open import Axiom.Extensionality.Propositional


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


module mp_search {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
                 (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
                 (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                 (F : Freeze {L} W C K P G N)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (CB : ChoiceBar W M C K P G X N V F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms3(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



-- This is the body of the fix in infSearch
infSearchL : Term → Term
infSearchL f =
  -- 1 is the recursive call and 0 is the number
  LAMBDA (LAMBDA (ITE (APPLY (shiftUp 0 (shiftUp 0 f)) (VAR 0))
                      (VAR 0)
                      (LET (SUC (VAR 0)) (APPLY (VAR 2) (VAR 0)))))

-- f is a function in #NAT!→BOOL
-- We're defining here the infinite search: fix(λR.λn.if f(n) then n else R(suc(n)))0
-- The closed version #infSearch is below
infSearch : Term → Term
infSearch f = APPLY (FIX (infSearchL f)) N0


#infSearchI : CTerm → CTerm → CTerm → CTerm
#infSearchI f R n =
  #ITE (#APPLY f n)
       n
       (#LET (#SUC n) (#[0]APPLY ⌞ R ⌟ #[0]VAR))


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


∈#BOOL→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
            → equalInType i w #BOOL a b
            → □· w (λ w' _ → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' a b)
∈#BOOL→ u w a b b∈ = eqInType-⇛-BOOL u w a b (fst b∈) (snd b∈)


#⇛!sameℕ-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a b : CTerm}
                 → #⇛!sameℕ w1 a b
                 → #⇛!sameℕ w2 a b
#⇛!sameℕ-mon {w1} {w2} e {a} {b} (n , c₁ , c₂) = n , ∀𝕎-mon e c₁ , ∀𝕎-mon e c₂


∈#NAT!→BOOL→ : (i : ℕ) (w : 𝕎·) (f : CTerm)
                 → ∈Type i w #NAT!→BOOL f
                 → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → #⇛!sameℕ w' n₁ n₂
                                 → □· w' (λ w' e → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f n₁) (#APPLY f n₂)))
∈#NAT!→BOOL→ i w f f∈ w1 e1 n₁ n₂ n∈ =
  ∈#BOOL→
    i w1 (#APPLY f n₁) (#APPLY f n₂)
    (equalInType-FUN→ f∈ w1 e1 n₁ n₂ (→equalInType-NAT! i w1 n₁ n₂ (Mod.∀𝕎-□ M λ w2 e2 → #⇛!sameℕ-mon e2 {n₁} {n₂} n∈)))


≤suc→⊎ : {a b : ℕ} → a ≤ suc b → a ≡ suc b ⊎ a ≤ b
≤suc→⊎ {0} {b} _≤_.z≤n = inj₂ _≤_.z≤n
≤suc→⊎ {suc 0} {0} (_≤_.s≤s _≤_.z≤n) = inj₁ refl
≤suc→⊎ {suc m} {suc b} (_≤_.s≤s h) with ≤suc→⊎ h
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p = inj₂ (_≤_.s≤s p)


∈#NAT!→BOOL≤→ : (i : ℕ) (w : 𝕎·) (f : CTerm) (n : ℕ)
                   → ∈Type i w #NAT!→BOOL f
                   → □· w (λ w' e → (m : ℕ) → m ≤ n → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
∈#NAT!→BOOL≤→ i w f 0 f∈ = Mod.∀𝕎-□Func M aw c
  where
    c : □· w (λ w' e → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f #N0) (#APPLY f #N0))
    c = ∈#NAT!→BOOL→ i w f f∈ w (⊑-refl· w) #N0 #N0 (#⇛!sameℕ-NUM w 0)

    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f #N0) (#APPLY f #N0)
                        → (m : ℕ) → m ≤ 0 → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
    aw w1 e1 h .ℕ.zero _≤_.z≤n = h
∈#NAT!→BOOL≤→ i w f (suc n) f∈ = ∀𝕎-□Func2 aw c ind
  where
    ind : □· w (λ w' e → (m : ℕ) → m ≤ n → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
    ind = ∈#NAT!→BOOL≤→ i w f n f∈

    c : □· w (λ w' e → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM (suc n))) (#APPLY f (#NUM (suc n))))
    c = ∈#NAT!→BOOL→ i w f f∈ w (⊑-refl· w) (#NUM (suc n)) (#NUM (suc n)) (#⇛!sameℕ-NUM w (suc n))

    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM (suc n))) (#APPLY f (#NUM (suc n)))
                        → ((m : ℕ) → m ≤ n → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
                        → (m : ℕ) → m ≤ suc n → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
    aw w1 e1 h1 h2 m len with ≤suc→⊎ len
    ... | inj₁ p rewrite p = h1
    ... | inj₂ p = h2 m p


∈#ASSERT₂→ : (i : ℕ) (w : 𝕎·) (t a b : CTerm)
               → equalInType i w (#ASSERT₂ t) a b
               → □· w (λ w' _ → Σ CTerm (λ u → t #⇛ #INL u at w'))
∈#ASSERT₂→ i w t a b a∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₂≡ t) a∈)))
  where
    aw1 : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType i w' #BOOL) w' a b
                         → Mod.□ M w' (↑wPred' (λ w'' _ → Σ CTerm (λ u → t #⇛ #INL u at w'')) e'))
    aw1 w1 e1 h = Mod.∀𝕎-□Func M aw2 (∈#BOOL→ i w1 t #BTRUE h)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' t #BTRUE
                              → ↑wPred' (λ w'' _ → Σ CTerm (λ u → t #⇛ #INL u at w'')) e1 w' e')
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , q)) z = x , c₁
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , q)) z = ⊥-elim (INLneqINR (≡CTerm (#compAllVal {#BTRUE} {#INR y} {w2} c₂ tt)))


∈#ASSERT₂→2 : (i : ℕ) (w : 𝕎·) (f k a b : CTerm) (n : ℕ)
                → ∈Type i w #NAT!→BOOL f
                → equalInType i w (#ASSERT₂ (#APPLY f k)) a b
                → k #⇛! #NUM n at w
                → □· w (λ w' _ → Σ CTerm (λ u → #APPLY f (#NUM n) #⇛ #INL u at w'))
∈#ASSERT₂→2 i w f k a b n f∈ a∈ ck =
  ∀𝕎-□Func2 aw h1 h2
  where
    h1 : □· w (λ w' e → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f k) (#APPLY f (#NUM n)))
    h1 = ∈#NAT!→BOOL→ i w f f∈ w (⊑-refl· w) k (#NUM n) (n , ck , #⇛!-refl {w} {#NUM n})

    h2 : □· w (λ w' _ → Σ CTerm (λ u → #APPLY f k #⇛ #INL u at w'))
    h2 = ∈#ASSERT₂→ i w (#APPLY f k) a b a∈

    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f k) (#APPLY f (#NUM n))
                        → (Σ CTerm (λ u → #APPLY f k #⇛ #INL u at w'))
                        → Σ CTerm (λ u → #APPLY f (#NUM n) #⇛ #INL u at w'))
    aw w1 e1 (x , y , inj₁ (c₁ , c₂ , q)) (u , d) = y , c₂
    aw w1 e1 (x , y , inj₂ (c₁ , c₂ , q)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛-val-det {w1} {#APPLY f k} {#INL u} {#INR x} tt tt d c₁)))


#infSearch⇛₁ : (w : 𝕎·) (f : CTerm) (n : ℕ)
                → #APPLY (#infSearchF f) (#NUM n) #⇛ #infSearchI f (#infSearchF f) (#NUM n) at w
#infSearch⇛₁ w f n w1 e1 = lift {!!}


-- by induction on n
-- add #¬Names f
mpSearch2 : (i : ℕ) (w : 𝕎·) (f u : CTerm) (n : ℕ)
            → ((m : ℕ) → m ≤ n → UNIONeq (equalInType i w #TRUE) (equalInType i w #TRUE) w (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
            → #APPLY f (#NUM n) #⇛ #INL u at w
            → Σ ℕ (λ m → Σ CTerm (λ u → m ≤ n × #infSearch f #⇛ #NUM m at w × #APPLY f (#NUM m) #⇛ #INL u at w))
mpSearch2 i w f u 0 hn ha = 0 , u , ≤-refl , {!!} , ha -- need to start proving lemmas about how infSearch computes
mpSearch2 i w f u (suc n) hn ha = {!!}


mpSearch1 : (i : ℕ) (w : 𝕎·) (f u : CTerm) (n : ℕ)
            → ((m : ℕ) → m ≤ n → UNIONeq (equalInType i w #TRUE) (equalInType i w #TRUE) w (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
            → #APPLY f (#NUM n) #⇛ #INL u at w
            → SUMeq (equalInType i w #NAT!) (λ a b ea → equalInType i w (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w (#infSearchP f) (#infSearchP f)
mpSearch1 i w f u n hn ha =
  #infSearch f , #infSearch f , #AX , #AX ,
  →equalInType-NAT! i w (#infSearch f) (#infSearch f) (Mod.∀𝕎-□ M p1) , -- How can we prove that it lives in #NAT! if f is not pure? Could we use #NAT for the impure version of MP? Negation is fine though
  #⇛-refl w (#infSearchP f) , #⇛-refl w (#infSearchP f) ,
  {!!}
-- For this we need to prove that (#infSearch f) computes to a number m ≤ n such that (#APPLY f (#NUM m)) computes to #INL
-- If f is not pure this might only be at a higher world, but if f is pure we can bring back the computation to the current world
-- ...so assume #¬Names f for this
  where
    p1 : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#infSearch f) (#infSearch f))
    p1 w1 e1 = {!!} -- use mpSearch2


mpSearch : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
           → ∈Type i w #NAT!→BOOL f
           → equalInType i w (#MP-right f) a₁ a₂
           → ∈Type i w (#MP-right2 f) (#infSearchP f)
mpSearch i w f a₁ a₂ f∈ a∈ =
  equalInType-local (Mod.∀𝕎-□Func M aw1 h1)
  where
    h1 : □· w (λ w' _ → inhType i w' (#MP-right2 f))
    h1 = equalInType-SQUASH→ a∈

    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2 f)
                         → ∈Type i w' (#MP-right2 f) (#infSearchP f))
    aw1 w1 e1 (t , t∈) =
      equalInType-local (Mod.∀𝕎-□Func M aw2 p∈) {--
        {!!}--}
      where
        p∈ : □· w1 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t)
        p∈ = equalInType-SUM→ t∈

        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
                              → ∈Type i w' (#MP-right2 f) (#infSearchP f))
        aw2 w2 e2 (n₁ , n₂ , x₁ , x₂ , n∈ , c₁ , c₂ , x∈) =
          equalInType-local (Mod.∀𝕎-□Func M aw3 (equalInType-NAT!→ i w2 n₁ n₂ n∈))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                                  → ∈Type i w' (#MP-right2 f) (#infSearchP f))
            aw3 w3 e3 (n , d₁ , d₂) =
              equalInType-SUM
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (∀𝕎-□Func2 aw4 h2 y∈)
              where
                y∈ : □· w3 (λ w' _ → Σ CTerm (λ u → #APPLY f (#NUM n) #⇛ #INL u at w'))
                y∈ = ∈#ASSERT₂→2 i w3 f n₁ x₁ x₂ n (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-mon x∈ w3 e3)) d₁

                h2 : □· w3 (λ w' e → (m : ℕ) → m ≤ n → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
                h2 = ∈#NAT!→BOOL≤→ i w3 f n (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3)))

                aw4 : ∀𝕎 w3 (λ w' e' → ((m : ℕ) → m ≤ n → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
                                      → (Σ CTerm (λ u → #APPLY f (#NUM n) #⇛ #INL u at w'))
                                      → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#infSearchP f) (#infSearchP f))
                aw4 w4 e4 hn ha = {!!} -- use mpSearch1

\end{code}
