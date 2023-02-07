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


module list {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
            (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
            (X : ChoiceExt W C)
            (N : NewChoice W C K G)
            (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_m(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)


-- 2nd component of APPEND
APPENDf : Term → Term → Term → Term
APPENDf k f x =
  LAMBDA (IFLT (VAR 0)
               (shiftUp 0 k)
               (APPLY (shiftUp 0 f) (VAR 0))
               (shiftUp 0 x))


-- appends a new value
APPEND : Term → Term → Term
APPEND l x =
  SPREAD l (PAIR (SUC (VAR 0))
                 (APPENDf (VAR 0) (VAR 1) (shiftUp 0 (shiftUp 0 x))))

{--
  PAIR (SUC k) (LAMBDA (IFLT (VAR 0) (shiftUp 0 k) (APPLY (shiftUp 0 f) (VAR 0)) (shiftUp 0 x)))
  where
    k : Term
    k = FST l

    f : Term
    f = SND l
--}


-- empty list (of numbers)
EMPTY : Term
EMPTY = PAIR (NUM 0) (LAMBDA (NUM 0))


LIST : Term → Term
LIST A = PROD NAT (FUN NAT A)


#LIST : CTerm → CTerm
#LIST A = #PROD #NAT (#FUN #NAT A)


#LAM0 : CTerm
#LAM0 = #LAMBDA (#[0]NUM 0)


#EMPTY : CTerm
#EMPTY = #PAIR (#NUM 0) #LAM0


-- APPEND's 2nd component
#APPENDf : CTerm → CTerm → CTerm → CTerm
#APPENDf n f x =
  #LAMBDA (#[0]IFLT #[0]VAR
                    (#[0]shiftUp0 n)
                    (#[0]APPLY (#[0]shiftUp0 f) #[0]VAR)
                    (#[0]shiftUp0 x))


#[0]APPENDf : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]APPENDf n f x =
  #[0]LAMBDA (#[1]IFLT #[1]VAR0
                       (#[1]shiftUp0 n)
                       (#[1]APPLY (#[1]shiftUp0 f) #[1]VAR0)
                       (#[1]shiftUp0 x))


#[1]APPENDf : CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]APPENDf n f x =
  #[1]LAMBDA (#[2]IFLT #[2]VAR0
                       (#[2]shiftUp0 n)
                       (#[2]APPLY (#[2]shiftUp0 f) #[2]VAR0)
                       (#[2]shiftUp0 x))


#[2]APPENDf : CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]APPENDf n f x =
  #[2]LAMBDA (#[3]IFLT #[3]VAR0
                       (#[3]shiftUp0 n)
                       (#[3]APPLY (#[3]shiftUp0 f) #[3]VAR0)
                       (#[3]shiftUp0 x))


#[3]APPENDf : CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]APPENDf n f x =
  #[3]LAMBDA (#[4]IFLT #[4]VAR0
                       (#[4]shiftUp0 n)
                       (#[4]APPLY (#[4]shiftUp0 f) #[4]VAR0)
                       (#[4]shiftUp0 x))


#[5]APPENDf : CTerm5 → CTerm5 → CTerm5 → CTerm5
#[5]APPENDf n f x =
  #[5]LAMBDA (#[6]IFLT #[6]VAR0
                       (#[6]shiftUp0 n)
                       (#[6]APPLY (#[6]shiftUp0 f) #[6]VAR0)
                       (#[6]shiftUp0 x))


#[6]APPENDf : CTerm6 → CTerm6 → CTerm6 → CTerm6
#[6]APPENDf n f x =
  #[6]LAMBDA (#[7]IFLT #[7]VAR0
                       (#[7]shiftUp0 n)
                       (#[7]APPLY (#[7]shiftUp0 f) #[7]VAR0)
                       (#[7]shiftUp0 x))


-- APPEND's body
#APPENDb : CTerm → CTerm1
#APPENDb x =
  #[1]PAIR (#[1]SUC #[1]VAR0)
           (#[1]LAMBDA (#[2]IFLT #[2]VAR0
                                 #[2]VAR1
                                 (#[2]APPLY #[2]VAR2 #[2]VAR0)
                                 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 x)))))


#APPEND : CTerm → CTerm → CTerm
#APPEND l x = #SPREAD l (#APPENDb x)


#[0]APPEND : CTerm0 → CTerm0 → CTerm0
#[0]APPEND l x =
  #[0]SPREAD l (#[2]PAIR (#[2]SUC #[2]VAR0)
                         (#[2]LAMBDA (#[3]IFLT #[3]VAR0
                                               #[3]VAR1
                                               (#[3]APPLY #[3]VAR2 #[3]VAR0)
                                               (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 x))))))


#[1]APPEND : CTerm1 → CTerm1 → CTerm1
#[1]APPEND l x =
  #[1]SPREAD l (#[3]PAIR (#[3]SUC #[3]VAR0)
                         (#[3]LAMBDA (#[4]IFLT #[4]VAR0
                                               #[4]VAR1
                                               (#[4]APPLY #[4]VAR2 #[4]VAR0)
                                               (#[4]shiftUp0 (#[3]shiftUp0 (#[2]shiftUp0 x))))))


#[2]APPEND : CTerm2 → CTerm2 → CTerm2
#[2]APPEND l x =
  #[2]SPREAD l (#[4]PAIR (#[4]SUC #[4]VAR0)
                         (#[4]LAMBDA (#[5]IFLT #[5]VAR0
                                               #[5]VAR1
                                               (#[5]APPLY #[5]VAR2 #[5]VAR0)
                                               (#[5]shiftUp0 (#[4]shiftUp0 (#[3]shiftUp0 x))))))


#[3]APPEND : CTerm3 → CTerm3 → CTerm3
#[3]APPEND l x =
  #[3]SPREAD l (#[5]PAIR (#[5]SUC #[5]VAR0)
                         (#[5]LAMBDA (#[6]IFLT #[6]VAR0
                                               #[6]VAR1
                                               (#[6]APPLY #[6]VAR2 #[6]VAR0)
                                               (#[6]shiftUp0 (#[5]shiftUp0 (#[4]shiftUp0 x))))))


#[4]APPEND : CTerm4 → CTerm4 → CTerm4
#[4]APPEND l x =
  #[4]SPREAD l (#[6]PAIR (#[6]SUC #[6]VAR0)
                         (#[6]LAMBDA (#[7]IFLT #[7]VAR0
                                               #[7]VAR1
                                               (#[7]APPLY #[7]VAR2 #[7]VAR0)
                                               (#[7]shiftUp0 (#[6]shiftUp0 (#[5]shiftUp0 x))))))


APPLY-APPENDf⇓ : (w : 𝕎·) (a f n m : CTerm) → #APPLY (#APPENDf a f n) m #⇓ #IFLT m a (#APPLY f m) n from w to w
APPLY-APPENDf⇓ w a f n m = 1 , ≡pair e refl
  where
    e : sub ⌜ m ⌝ ⌜ #[0]IFLT #[0]VAR (#[0]shiftUp0 a) (#[0]APPLY (#[0]shiftUp0 f) #[0]VAR) (#[0]shiftUp0 n) ⌝
        ≡ ⌜ #IFLT m a (#APPLY f m) n ⌝
    e rewrite #shiftUp 0 m
            | #shiftUp 0 a
            | #shiftUp 0 f
            | #shiftUp 0 n
            | #shiftDown 0 m
            | #subv 0 ⌜ m ⌝ ⌜ a ⌝ (CTerm.closed a)
            | #subv 0 ⌜ m ⌝ ⌜ f ⌝ (CTerm.closed f)
            | #subv 0 ⌜ m ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 m
            | #shiftDown 0 a
            | #shiftDown 0 f
            | #shiftDown 0 n = refl


APPLY-APPENDf⇛ : (w : 𝕎·) (a f n m : CTerm) → #APPLY (#APPENDf a f n) m #⇛ #IFLT m a (#APPLY f m) n at w
APPLY-APPENDf⇛ w a f n m w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} (APPLY-APPENDf⇓ w1 a f n m))


LISTNATeq : (i : ℕ) → wper
LISTNATeq i w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    NATeq w a1 a2
    × equalInType i w #BAIRE b1 b2
    × f #⇛ (#PAIR a1 b1) at w
    × g #⇛ (#PAIR a2 b2) at w))))


equalInType-LIST-NAT→ : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                         → equalInType i w (#LIST #NAT) f g
                         → □· w (λ w' _ → LISTNATeq i w' f g)
equalInType-LIST-NAT→ i w f g eqi = Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-PROD→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → PRODeq (equalInType i w' #NAT) (equalInType i w' (#FUN #NAT #NAT)) w' f g
                       → □· w' (↑wPred' (λ w'' _ → LISTNATeq i w'' f g) e'))
    aw w1 e1 (k1 , k2 , f1 , f2 , ek , ef , c1 , c2) = Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 k1 k2 ek)
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' k1 k2
                             → ↑wPred' (λ w'' _ → LISTNATeq i w'' f g) e1 w' e')
        aw1 w2 e2 ek' e3 = k1 , k2 , f1 , f2 , ek' , equalInType-mon ef w2 e2 , ∀𝕎-mon e2 c1 , ∀𝕎-mon e2 c2


→equalInType-LIST-NAT : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                         → □· w (λ w' _ → LISTNATeq i w' f g)
                         → equalInType i w (#LIST #NAT) f g
→equalInType-LIST-NAT i w f g eqi =
  equalInType-PROD eqTypesNAT eqTypesBAIRE (Mod.∀𝕎-□Func M aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → LISTNATeq i w' f g
                        → PRODeq (equalInType i w' #NAT) (equalInType i w' #BAIRE) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , x , y , c1 , c2) =
      a1 , a2 , b1 , b2 ,
      →equalInType-NAT i w1 a1 a2 (Mod.∀𝕎-□ M λ w2 e2 → NATeq-mon {w1} {w2} e2 {a1} {a2} x) ,
      y , c1 , c2


→NATeq-IFLT-NUM : {w : 𝕎·} {i j : ℕ} {c1 c2 d1 d2 : CTerm}
                   → NATeq w c1 c2
                   → NATeq w d1 d2
                   → NATeq w (#IFLT (#NUM i) (#NUM j) c1 d1) (#IFLT (#NUM i) (#NUM j) c2 d2)
→NATeq-IFLT-NUM {w} {i} {j} {c1} {c2} {d1} {d2} x y with i <? j
... | yes p = NATeq⇛
                {w} {#IFLT (#NUM i) (#NUM j) c1 d1} {c1} {#IFLT (#NUM i) (#NUM j) c2 d2} {c2}
                (IFLT⇛< {j} {i} {w} {⌜ c1 ⌝} {⌜ d1 ⌝} p)
                (IFLT⇛< {j} {i} {w} {⌜ c2 ⌝} {⌜ d2 ⌝} p)
                x
... | no p = NATeq⇛ {w} {#IFLT (#NUM i) (#NUM j) c1 d1} {d1}
               {#IFLT (#NUM i) (#NUM j) c2 d2} {d2}
               (IFLT⇛¬< {j} {i} {w} {⌜ c1 ⌝} {⌜ d1 ⌝} p)
               (IFLT⇛¬< {j} {i} {w} {⌜ c2 ⌝} {⌜ d2 ⌝} p)
               y


→NATeq-IFLT : {w : 𝕎·} {a1 a2 b1 b2 c1 c2 d1 d2 : CTerm}
               → NATeq w a1 a2
               → NATeq w b1 b2
               → NATeq w c1 c2
               → NATeq w d1 d2
               → NATeq w (#IFLT a1 b1 c1 d1) (#IFLT a2 b2 c2 d2)
→NATeq-IFLT {w} {a1} {a2} {b1} {b2} {c1} {c2} {d1} {d2} (n1 , x1 , x2) (n2 , y1 , y2) z1 z2 =
  NATeq⇛
    {w}
    {#IFLT a1 b1 c1 d1} {#IFLT (#NUM n1) (#NUM n2) c1 d1}
    {#IFLT a2 b2 c2 d2} {#IFLT (#NUM n1) (#NUM n2) c2 d2}
    (IFLT⇛₃ {w} {n1} {n2} {⌜ a1 ⌝} {⌜ b1 ⌝} {⌜ c1 ⌝} {⌜ d1 ⌝} x1 y1)
    (IFLT⇛₃ {w} {n1} {n2} {⌜ a2 ⌝} {⌜ b2 ⌝} {⌜ c2 ⌝} {⌜ d2 ⌝} x2 y2)
    (→NATeq-IFLT-NUM {w} {n1} {n2} {c1} {c2} {d1} {d2} z1 z2)


APPENDf∈BAIRE : {i : ℕ} {w : 𝕎·} {a1 a2 f1 f2 n1 n2 : CTerm}
                 → equalInType i w #NAT a1 a2
                 → equalInType i w #NAT n1 n2
                 → equalInType i w #BAIRE f1 f2
                 → equalInType i w #BAIRE (#APPENDf a1 f1 n1) (#APPENDf a2 f2 n2)
APPENDf∈BAIRE {i} {w} {a1} {a2} {f1} {f2} {n1} {n2} a∈ n∈ f∈ =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY (#APPENDf a1 f1 n1) a₁) (#APPLY (#APPENDf a2 f2 n2) a₂))
    aw w1 e1 m1 m2 m∈ =
      →equalInType-NAT
        i w1
        (#APPLY (#APPENDf a1 f1 n1) m1)
        (#APPLY (#APPENDf a2 f2 n2) m2)
        (∀𝕎-□Func4 aw1 f∈1 n∈1 a∈1 m∈1)
      where
        f∈1 : □· w1 (λ w' _ → NATeq w' (#APPLY f1 m1) (#APPLY f2 m2))
        f∈1 = equalInType-NAT→ i w1 (#APPLY f1 m1) (#APPLY f2 m2) (∈BAIRE→ {i} {w1} (equalInType-mon f∈ w1 e1) m∈)

        n∈1 : □· w1 (λ w' _ → NATeq w' n1 n2)
        n∈1 = equalInType-NAT→ i w1 n1 n2 (equalInType-mon n∈ w1 e1)

        a∈1 : □· w1 (λ w' _ → NATeq w' a1 a2)
        a∈1 = equalInType-NAT→ i w1 a1 a2 (equalInType-mon a∈ w1 e1)

        m∈1 : □· w1 (λ w' _ → NATeq w' m1 m2)
        m∈1 = equalInType-NAT→ i w1 m1 m2 m∈

        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' (#APPLY f1 m1) (#APPLY f2 m2)
                              → NATeq w' n1 n2 → NATeq w' a1 a2 → NATeq w' m1 m2
                              → NATeq w' (#APPLY (#APPENDf a1 f1 n1) m1) (#APPLY (#APPENDf a2 f2 n2) m2))
        aw1 w2 e2 if ix ia im =
          NATeq⇛
            {w2}
            {#APPLY (#APPENDf a1 f1 n1) m1} {#IFLT m1 a1 (#APPLY f1 m1) n1}
            {#APPLY (#APPENDf a2 f2 n2) m2} {#IFLT m2 a2 (#APPLY f2 m2) n2}
            (APPLY-APPENDf⇛ w2 a1 f1 n1 m1) (APPLY-APPENDf⇛ w2 a2 f2 n2 m2) c
          where
            c : NATeq w2 (#IFLT m1 a1 (#APPLY f1 m1) n1) (#IFLT m2 a2 (#APPLY f2 m2) n2)
            c = →NATeq-IFLT {w2} {m1} {m2} {a1} {a2} {#APPLY f1 m1} {#APPLY f2 m2} {n1} {n2} im ia if ix


#APPEND-PAIR⇛PAIR : (w : 𝕎·) (a f n : CTerm) → #APPEND (#PAIR a f) n #⇛ #PAIR (#SUC a) (#APPENDf a f n) at w
#APPEND-PAIR⇛PAIR w a f n w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} (1 , ≡pair e refl))
  where
    e : sub ⌜ f ⌝ (sub ⌜ a ⌝ ⌜ #APPENDb n ⌝) ≡ ⌜ #PAIR (#SUC a) (#APPENDf a f n) ⌝
    e rewrite #shiftUp 0 f
            | #shiftUp 0 f
            | #shiftUp 1 f
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 1 a
            | #shiftUp 0 n
            | #shiftUp 0 n
            | #shiftUp 0 n
            | #shiftDown 0 a
            | #shiftDown 1 a
            | #shiftDown 1 f
            | #subv 0 ⌜ f ⌝ ⌜ a ⌝ (CTerm.closed a)
            | #subv 1 ⌜ f ⌝ ⌜ a ⌝ (CTerm.closed a)
            | #subv 1 ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 a
            | #shiftDown 1 n
            | #subv 1 ⌜ f ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 1 a
            | #shiftDown 1 n = refl


#APPEND⇛PAIR : (w : 𝕎·) (l n a f : CTerm)
                → l #⇛ #PAIR a f at w
                → #APPEND l n #⇛ #PAIR (#SUC a) (#APPENDf a f n) at w
#APPEND⇛PAIR w l n a f comp =
  #⇛-trans
    {w} {#APPEND l n} {#APPEND (#PAIR a f) n} {#PAIR (#SUC a) (#APPENDf a f n)}
    (SPREAD⇛₁ {w} {⌜ l ⌝} {⌜ #PAIR a f ⌝} {⌜ #APPENDb n ⌝} comp)
    (#APPEND-PAIR⇛PAIR w a f n)


APPEND∈LIST : (i : ℕ) (w : 𝕎·) (l n : CTerm)
               → ∈Type i w (#LIST #NAT) l
               → ∈Type i w #NAT n
               → ∈Type i w (#LIST #NAT) (#APPEND l n)
APPEND∈LIST i w l n ∈l ∈n =
  →equalInType-LIST-NAT i w (#APPEND l n) (#APPEND l n) (∀𝕎-□Func2 aw ∈l1 ∈n1)
  where
    ∈l1 : □· w (λ w' _ → LISTNATeq i w' l l)
    ∈l1 = equalInType-LIST-NAT→ i w l l ∈l

    ∈n1 : □· w (λ w' _ → NATmem w' n)
    ∈n1 = equalInType-NAT→ i w n n ∈n

    aw : ∀𝕎 w (λ w' e' → LISTNATeq i w' l l → NATmem w' n → LISTNATeq i w' (#APPEND l n) (#APPEND l n))
    aw w1 e1 (a1 , a2 , f1 , f2 , (m , z1 , z2) , x2 , c1 , c2) (k , d1 , d2) =
      #SUC a1 , #SUC a2 , #APPENDf a1 f1 n , #APPENDf a2 f2 n ,
      (suc m , SUC⇛₂ {w1} {⌜ a1 ⌝} {m} z1 , SUC⇛₂ {w1} {⌜ a2 ⌝} {m} z2) ,
      APPENDf∈BAIRE {i} {w1} {a1} {a2} {f1} {f2} {n} {n} (⇛NUMs→equalInType-NAT i w1 a1 a2 m z1 z2) (equalInType-mon ∈n w1 e1) x2 ,
      #APPEND⇛PAIR w1 l n a1 f1 c1 ,
      #APPEND⇛PAIR w1 l n a2 f2 c2


NATeq-NUM : (w : 𝕎·) (k : ℕ) → NATeq w (#NUM k) (#NUM k)
NATeq-NUM w k = k , #⇛-refl w (#NUM k) , #⇛-refl w (#NUM k)


LAM0⇛NUM0 : (w : 𝕎·) (a : CTerm) → #APPLY #LAM0 a #⇛! #NUM 0 at w
LAM0⇛NUM0 w a w1 e1 = lift (1 , refl)


LAM0∈BAIRE : (i : ℕ) (w : 𝕎·) → equalInType i w #BAIRE #LAM0 #LAM0
LAM0∈BAIRE i w =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       →  equalInType i w' #NAT (#APPLY #LAM0 a₁) (#APPLY #LAM0 a₂))
    aw w1 e1 a b eqa = →equalInType-NAT i w1 (#APPLY #LAM0 a) (#APPLY #LAM0 b) (Mod.∀𝕎-□ M aw1)
      where
        aw1 : ∀𝕎 w1 (λ w' _ → NATeq w' (#APPLY #LAM0 a) (#APPLY #LAM0 b))
        aw1 w2 e2 =
          0 ,
          #⇛!-#⇛ {w2} {#APPLY #LAM0 a} {#NUM 0} (LAM0⇛NUM0 w2 a) ,
          #⇛!-#⇛ {w2} {#APPLY #LAM0 b} {#NUM 0} (LAM0⇛NUM0 w2 b)


EMPTY∈LIST : (i : ℕ) (w : 𝕎·) → ∈Type i w (#LIST #NAT) #EMPTY
EMPTY∈LIST i w = →equalInType-LIST-NAT i w #EMPTY #EMPTY (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → LISTNATeq i w' #EMPTY #EMPTY)
    aw w1 e1 =
      #NUM 0 , #NUM 0 , #LAM0 , #LAM0 ,
      NATeq-NUM w1 0 ,
      LAM0∈BAIRE i w1 ,
      #⇛-refl w1 #EMPTY , #⇛-refl w1 #EMPTY


#⇛∈LIST : (i : ℕ) (w : 𝕎·) (l k f : CTerm) (n : ℕ)
            → l #⇛ #PAIR k f at w
            → k #⇛ #NUM n at w
            → ∈Type i w #BAIRE f
            → ∈Type i w (#LIST #NAT) l
#⇛∈LIST i w l k f n compl compk f∈ =
  →equalInType-LIST-NAT
    i w l l
    (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → LISTNATeq i w' l l)
    aw w1 e1 =
      k , k , f , f ,
      (n , ∀𝕎-mon e1 compk , ∀𝕎-mon e1 compk) ,
      equalInType-mon f∈ w1 e1 ,
      ∀𝕎-mon e1 compl , ∀𝕎-mon e1 compl


APPLY⇓₁ : {w : 𝕎·} {a b : Term} (c : Term)
         → a ⇓ b at w
         → APPLY a c ⇓ APPLY b c at w
APPLY⇓₁ {w} {a} {b} c comp = ⇓-from-to→⇓ (APPLY⇓ {w} {fst comp'} {a} {b} c (snd comp'))
  where
    comp' : Σ 𝕎· (λ w' → a ⇓ b from w to w')
    comp' = ⇓→from-to {w} {a} {b} comp


#APPLY#⇛ : {w : 𝕎·} {a b : CTerm} (c : CTerm)
            → a #⇛ b at w
            → #APPLY a c #⇛ #APPLY b c at w
#APPLY#⇛ {w} {a} {b} c comp w1 e1 = lift (APPLY⇓₁ {w1} {⌜ a ⌝} {⌜ b ⌝} ⌜ c ⌝ (lower (comp w1 e1)))


∈LIST→SND : (i : ℕ) (w : 𝕎·) (l : CTerm)
              → ∈Type i w (#LIST #NAT) l
              → ∈Type i w #BAIRE (#SND l)
∈LIST→SND i w l l∈ =
  equalInType-local (Mod.∀𝕎-□Func M aw (equalInType-LIST-NAT→ i w l l l∈))
  where
    aw : ∀𝕎 w (λ w' e' → LISTNATeq i w' l l → equalInType i w' #BAIRE (#SND l) (#SND l))
    aw w1 e1 (a1 , a2 , b1 , b2 , aeq , beq , c1 , c2) =
      ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw1)
      where
        aw1 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                             → equalInType i w' #NAT (#APPLY (#SND l) a₁) (#APPLY (#SND l) a₂))
        aw1 w2 e2 a₁ a₂ ea =
          equalInType-NAT-#⇛
            i w2
            (#APPLY (#SND l) a₁) (#APPLY b1 a₁)
            (#APPLY (#SND l) a₂) (#APPLY b2 a₂)
            (#APPLY#⇛ {w2} {#SND l} {b1} a₁ (#⇛-SND-PAIR l a1 b1 w2 (∀𝕎-mon e2 c1)))
            (#APPLY#⇛ {w2} {#SND l} {b2} a₂ (#⇛-SND-PAIR l a2 b2 w2 (∀𝕎-mon e2 c2)))
            (equalInType-FUN→ {i} {w1} {#NAT} {#NAT} {b1} {b2} beq w2 e2 a₁ a₂ ea)

\end{code}
