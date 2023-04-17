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
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
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


module props5 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
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
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_m(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)



-- MOVE to computation
#⇓-trans₁ : {w w' : 𝕎·} {a b c : CTerm} → a #⇓ b from w to w' → b #⇓ c at w' → a #⇓ c at w
#⇓-trans₁ {w} {w'} {a} {b} {c} c₁ c₂ = ⇓-trans₁ {w} {w'} {⌜ a ⌝} {⌜ b ⌝} {⌜ c ⌝} c₁ c₂


-- MOVE to forcing
NATmem : (w : 𝕎·) → CTerm → Set(lsuc(L))
NATmem w t = NATeq w t t


PROD : Term → Term → Term
PROD a b = SUM a (shiftUp 0 b)


#PROD : CTerm → CTerm → CTerm
#PROD a b = ct (PROD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # PROD ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | #shiftUp 0 b | lowerVars-fvars-CTerm≡[] b = refl


#PROD≡#SUM : (A B : CTerm) → #PROD A B ≡ #SUM A ⌞ B ⌟
#PROD≡#SUM A B = CTerm≡ e
  where
    e : PROD ⌜ A ⌝ ⌜ B ⌝ ≡ SUM ⌜ A ⌝ ⌜ B ⌝
    e rewrite #shiftUp 0 B = refl


PRODeq : (eqa eqb : per) → wper
PRODeq eqa eqb w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    eqa a1 a2
    × eqb b1 b2
    × f #⇛ (#PAIR a1 b1) at w
    × g #⇛ (#PAIR a2 b2) at w))))


equalInType-PROD : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                  → isType u w A
                  → isType u w B
                  → □· w (λ w' _ → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g)
                  → equalInType u w (#PROD A B) f g
equalInType-PROD {u} {w} {A} {B} {f} {g} ha hb eqi =
  ≡CTerm→equalInType (sym (#PROD≡#SUM A B)) (equalInType-SUM ha' hb' eqi')
  where
    ha' : ∀𝕎 w (λ w' _ → isType u w' A)
    ha' w1 e1 = eqTypes-mon (uni u) ha w1 e1

    hb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ B ⌟))
    hb' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ B = eqTypes-mon (uni u) hb w1 e1

    aw : ∀𝕎 w (λ w' e' → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g
                       → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a (CTerm→CTerm0 B))) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , ea , eb , c1 , c2) = a1 , a2 , b1 , b2 , ea , c1 , c2 , eb'
      where
        eb' : equalInType u w1 (sub0 a1 (CTerm→CTerm0 B)) b1 b2
        eb' rewrite sub0⌞⌟ a1 B = eb

    eqi' : □· w (λ w' _ → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a ⌞ B ⌟)) w' f g)
    eqi' = Mod.∀𝕎-□Func M aw eqi


equalInType-PROD→ : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                     → equalInType u w (#PROD A B) f g
                     → □· w (λ w' _ → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g)
equalInType-PROD→ {u} {w} {A} {B} {f} {g} eqi =
  Mod.∀𝕎-□Func M aw (equalInType-SUM→ {u} {w} {A} {⌞ B ⌟} {f} {g} (≡CTerm→equalInType (#PROD≡#SUM A B) eqi))
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a (CTerm→CTerm0 B))) w' f g
                        → PRODeq (equalInType u w' A) (equalInType u w' B) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , ea , c1 , c2 , eb) rewrite sub0⌞⌟ a1 B = a1 , a2 , b1 , b2 , ea , eb , c1 , c2


UNION! : Term → Term → Term
UNION! a b = TCONST (UNION a b)


#UNION! : CTerm → CTerm → CTerm
#UNION! a b = #TCONST (#UNION a b)


UNION!eq : (eqa eqb : per) → wper
UNION!eq eqa eqb w t1 t2  =
  Σ CTerm (λ a → Σ CTerm (λ b →
    (t1 #⇛! (#INL a) at w × t2 #⇛! (#INL b) at w × eqa a b)
    ⊎
    (t1 #⇛! (#INR a) at w × t2 #⇛! (#INR b) at w × eqb a b)))


#⇓→#⇓!-mon : {w w' : 𝕎·} {a : CTerm}
             → w ⊑· w'
             → #⇓→#⇓! w a
             → #⇓→#⇓! w' a
#⇓→#⇓!-mon {w} {w'} {a} e h w1 e1 = lift (lower (h w1 (⊑-trans· e e1)))


#⇛→#⇛!⊑ : {w w' : 𝕎·} {a b : CTerm}
             → w ⊑· w'
             → #⇓→#⇓! w a
             → #isValue b
             → a #⇛ b at w'
             → a #⇛! b at w'
#⇛→#⇛!⊑ {w} {w'} {a} {b} e h isv comp =
  #⇛→#⇛! {w'} {a} {b} (#⇓→#⇓!-mon {w} {w'} {a} e h) isv comp


equalInType-UNION!→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#UNION! A B) a b
                       → □· w (λ w' _ → UNION!eq (equalInType n w' A) (equalInType n w' B) w' a b)
equalInType-UNION!→ {n} {w} {A} {B} {a} {b} equ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInTypeTCONST→ equ))
  where
    aw1 : ∀𝕎 w (λ w' e' → TCONSTeq (equalInType n w' (#UNION A B)) w' a b
                        → Mod.□ M w' (↑wPred' (λ w'' _ → UNION!eq (equalInType n w'' A) (equalInType n w'' B) w'' a b) e'))
    aw1 w1 e1 (equ1 , c1 , c2) = Mod.∀𝕎-□Func M aw2 (equalInType-UNION→ {n} {w1} {A} {B} equ1)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → UNIONeq (equalInType n w' A) (equalInType n w' B) w' a b
                              → ↑wPred' (λ w'' _ → UNION!eq (equalInType n w'' A) (equalInType n w'' B) w'' a b) e1 w' e')
        aw2 w2 e2 (x , y , inj₁ (d1 , d2 , equ2)) z =
          x , y , inj₁ (#⇛→#⇛!⊑ {w1} {w2} {a} {#INL x} e2 c1 tt d1 ,
                        #⇛→#⇛!⊑ {w1} {w2} {b} {#INL y} e2 c2 tt d2 ,
                        equ2)
        aw2 w2 e2 (x , y , inj₂ (d1 , d2 , equ2)) z =
          x , y , inj₂ (#⇛→#⇛!⊑ {w1} {w2} {a} {#INR x} e2 c1 tt d1 ,
                        #⇛→#⇛!⊑ {w1} {w2} {b} {#INR y} e2 c2 tt d2 ,
                        equ2)


#⇛!→#⇓→#⇓! : {w : 𝕎·} {a v : CTerm}
                → #isValue v
                → a #⇛! v at w
                → #⇓→#⇓! w a
#⇛!→#⇓→#⇓! {w} {a} {v} isv comp w1 e1 = lift j
  where
    j : (u : CTerm) (w2 : 𝕎·) → #isValue u → a #⇓ u from w1 to w2 → a #⇓! u at w1
    j u w2 isu comp1 = c
      where
        c : a #⇓! u at w1
        c rewrite #⇓-val-det {w1} {a} {u} {v} isu isv
                             (#⇓from-to→#⇓ {w1} {w2} {a} {u} comp1)
                             (#⇓from-to→#⇓ {w1} {w1} {a} {v} (lower (comp w1 e1))) = lower (comp w1 e1)


→equalInType-UNION! : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → UNION!eq (equalInType n w' A) (equalInType n w' B) w' a b)
                       → equalInType n w (#UNION! A B) a b
→equalInType-UNION! {n} {w} {A} {B} {a} {b} ista istb equ =
  →equalInTypeTCONST (Mod.∀𝕎-□Func M aw equ)
  where
    aw : ∀𝕎 w (λ w' e' → UNION!eq (equalInType n w' A) (equalInType n w' B) w' a b
                        → TCONSTeq (equalInType n w' (#UNION A B)) w' a b)
    aw w1 e1 (x , y , inj₁ (c1 , c2 , equ1)) =
      →equalInType-UNION
        (eqTypes-mon (uni n) ista w1 e1)
        (eqTypes-mon (uni n) istb w1 e1)
        (Mod.∀𝕎-□ M (λ w2 e2 → x , y , inj₁ (#⇛!-#⇛ {w2} {a} {#INL x} (∀𝕎-mon e2 c1) ,
                                               #⇛!-#⇛ {w2} {b} {#INL y} (∀𝕎-mon e2 c2) ,
                                               equalInType-mon equ1 w2 e2))) ,
      #⇛!→#⇓→#⇓! {w1} {a} {#INL x} tt c1 , #⇛!→#⇓→#⇓! {w1} {b} {#INL y} tt c2
    aw w1 e1 (x , y , inj₂ (c1 , c2 , equ1)) =
      →equalInType-UNION
        (eqTypes-mon (uni n) ista w1 e1)
        (eqTypes-mon (uni n) istb w1 e1)
        (Mod.∀𝕎-□ M (λ w2 e2 → x , y , inj₂ (#⇛!-#⇛ {w2} {a} {#INR x} (∀𝕎-mon e2 c1) ,
                                               #⇛!-#⇛ {w2} {b} {#INR y} (∀𝕎-mon e2 c2) ,
                                               equalInType-mon equ1 w2 e2))) ,
      #⇛!→#⇓→#⇓! {w1} {a} {#INR x} tt c1 , #⇛!→#⇓→#⇓! {w1} {b} {#INR y} tt c2


eqTypesUNION!← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w C D
                  → equalTypes i w (#UNION! A C) (#UNION! B D)
eqTypesUNION!← {w} {i} {A} {B} {C} {D} eq1 eq2 = eqTypesTCONST← (eqTypesUNION← eq1 eq2)


NATeq-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a1 a2 : CTerm}
            → NATeq w1 a1 a2
            → NATeq w2 a1 a2
NATeq-mon {w1} {w2} e {a1} {a2} (n , c1 , c2) = n , ∀𝕎-mon e c1 , ∀𝕎-mon e c2


equalInType-NAT-#⇛ : (i : ℕ) (w : 𝕎·) (a1 a2 b1 b2 : CTerm)
                      → a1 #⇛ a2 at w
                      → b1 #⇛ b2 at w
                      → equalInType i w #NAT a2 b2
                      → equalInType i w #NAT a1 b1
equalInType-NAT-#⇛ i w a1 a2 b1 b2 c1 c2 eqi =
  →equalInType-NAT i w a1 b1 (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w a2 b2 eqi))
  where
    aw : ∀𝕎 w (λ w' e' → NATeq w' a2 b2 → NATeq w' a1 b1)
    aw w1 e1 (n , d1 , d2) =
      n ,
      ⇛-trans {w1} {⌜ a1 ⌝} {⌜ a2 ⌝} {NUM n} (∀𝕎-mon e1 c1) d1 ,
      ⇛-trans {w1} {⌜ b1 ⌝} {⌜ b2 ⌝} {NUM n} (∀𝕎-mon e1 c2) d2


∈BAIRE→ : {i : ℕ} {w : 𝕎·} {f₁ f₂ n₁ n₂ : CTerm}
                → equalInType i w #BAIRE f₁ f₂
                → equalInType i w #NAT n₁ n₂
                → equalInType i w #NAT (#APPLY f₁ n₁) (#APPLY f₂ n₂)
∈BAIRE→ {i} {w} {f₁} {f₂} {n₁} {n₂} ∈f ∈n =
  equalInType-FUN→
    {i} {w} {#NAT} {#NAT} {f₁} {f₂} (≡CTerm→equalInType #BAIRE≡ ∈f) w (⊑-refl· _) n₁ n₂
    ∈n


NATeq⇛ : {w : 𝕎·} {a1 a2 b1 b2 : CTerm}
          → a1 #⇛ a2 at w
          → b1 #⇛ b2 at w
          → NATeq w a2 b2
          → NATeq w a1 b1
NATeq⇛ {w} {a1} {a2} {b1} {b2} c1 c2 (n , z1 , z2) = n , ⇛-trans c1 z1 , ⇛-trans c2 z2

\end{code}
