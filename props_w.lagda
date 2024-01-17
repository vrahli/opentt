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
--open import choiceBar
open import encode


module props_w {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
               (C : Choice)
               (K : Compatible {L} W C)
               (G : GetChoice {L} W C K)
               (X : ChoiceExt W C)
               (N : NewChoice {L} W C K G)
               (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC) using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
open import props4(W)(M)(C)(K)(G)(X)(N)(EC)


WT₀ : Term → Term → Term
WT₀ A B = WT A B NOREAD


#WT₀ : CTerm → CTerm0 → CTerm
#WT₀ A B = #WT A B #NOREAD


MT₀ : Term → Term → Term
MT₀ A B = MT A B NOREAD


#MT₀ : CTerm → CTerm0 → CTerm
#MT₀ A B = #MT A B #NOREAD


WT₁ : Term → Term → Term
WT₁ A B = WT A B TRUE


#WT₁ : CTerm → CTerm0 → CTerm
#WT₁ A B = #WT A B #TRUE


MT₁ : Term → Term → Term
MT₁ A B = MT A B TRUE


#MT₁ : CTerm → CTerm0 → CTerm
#MT₁ A B = #MT A B #TRUE


data weq₀ (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
data weq₀ eqa eqb w t1 t2 where
  weqC₀ : (a1 f1 a2 f2 : CTerm) (e : eqa a1 a2)
             → t1 #⇛ (#SUP a1 f1) at w
             → t2 #⇛ (#SUP a2 f2) at w
             → ((b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → weq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))
             → weq₀ eqa eqb w t1 t2


record meq₀ (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
record meq₀ eqa eqb w t1 t2 where
  coinductive
  field
    meqC₀ : Σ CTerm (λ a1 → Σ CTerm (λ f1 → Σ CTerm (λ a2 → Σ CTerm (λ f2 → Σ  (eqa a1 a2) (λ e →
            t1 #⇛ (#SUP a1 f1) at w
            × t2 #⇛ (#SUP a2 f2) at w
            × ((b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → meq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2)))))))


data weq₁ (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
data weq₁ eqa eqb w t1 t2 where
  weqC₁ : (a1 f1 a2 f2 : CTerm) (e : eqa a1 a2)
             → t1 #⇓ (#SUP a1 f1) at w
             → t2 #⇓ (#SUP a2 f2) at w
             → ((b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → weq₁ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))
             → weq₁ eqa eqb w t1 t2


record meq₁ (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
record meq₁ eqa eqb w t1 t2 where
  coinductive
  field
    meqC₁ : Σ CTerm (λ a1 → Σ CTerm (λ f1 → Σ CTerm (λ a2 → Σ CTerm (λ f2 → Σ  (eqa a1 a2) (λ e →
            t1 #⇓ (#SUP a1 f1) at w
            × t2 #⇓ (#SUP a2 f2) at w
            × ((b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → meq₁ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2)))))))


#⇛→#⇓→#⇛ : {w : 𝕎·} {a v : CTerm}
         → #isValue v
         → a #⇛ v at w
         → #⇓→#⇛ w a
#⇛→#⇓→#⇛ {w} {a} {v} isv comp w1 e1 v' isv' comp'
  rewrite #⇓-val-det {w1} {a} {v'} {v} isv' isv comp' (lower (comp w1 e1))
  = ∀𝕎-mon e1 comp


#⇛→NOREADeq : {w : 𝕎·} {a b u v : CTerm}
            → #isValue u
            → #isValue v
            → a #⇛ u at w
            → b #⇛ v at w
            → NOREADeq w a b
#⇛→NOREADeq {w} {a} {b} {u} {v} isvu isvv c1 c2 =
  #⇛→#⇓→#⇛ {w} {a} {u} isvu c1 , #⇛→#⇓→#⇛ {w} {b} {v} isvv c2


-- TODO: It would be better to wrap the computations in weq and weq₀ with □
→weq₀ : (kb : K□) (i : ℕ) (w : 𝕎·) (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t u : CTerm)
      → weq eqa eqb (equalInType i w #NOREAD) w t u
      → weq₀ eqa eqb w t u
→weq₀ kb i w eqa eqb t u (weqC a1 f1 a2 f2 e c₁ c₂ ec q) =
  weqC₀ a1 f1 a2 f2 e
    (fst ec1 w (⊑-refl· w) (#SUP a1 f1) tt c₁)
    (snd ec1 w (⊑-refl· w) (#SUP a2 f2) tt c₂)
    (λ b1 b2 b∈ → →weq₀ kb i w eqa eqb (#APPLY f1 b1) (#APPLY f2 b2) (q b1 b2 b∈))
  where
    ec1 : NOREADeq w t u
    ec1 = kb (equalInTypeNOREAD→ ec) w (⊑-refl· w)


weq₀→ : (i : ℕ) (w : 𝕎·) (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t u : CTerm)
      → weq₀ eqa eqb w t u
      → weq eqa eqb (equalInType i w #NOREAD) w t u
weq₀→ i w eqa eqb t u (weqC₀ a1 f1 a2 f2 e c₁ c₂ q) =
  weqC a1 f1 a2 f2 e (lower (c₁ w (⊑-refl· w))) (lower (c₂ w (⊑-refl· w)))
    (→equalInTypeNOREAD (Mod.∀𝕎-□ M (λ w1 e1 → #⇛→NOREADeq {w1} {t} {u} {#SUP a1 f1} {#SUP a2 f2} tt tt (∀𝕎-mon e1 c₁) (∀𝕎-mon e1 c₂))))
    (λ b1 b2 b∈ → weq₀→ i w eqa eqb (#APPLY f1 b1) (#APPLY f2 b2) (q _ _ b∈))


→meq₀ : (kb : K□) (i : ℕ) (w : 𝕎·) (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t u : CTerm)
      → meq eqa eqb (equalInType i w #NOREAD) w t u
      → meq₀ eqa eqb w t u
meq₀.meqC₀ (→meq₀ kb i w eqa eqb t u h) with meq.meqC h
... | a1 , f1 , a2 , f2 , e1 , c1 , c2 , ec , p =
  a1 , f1 , a2 , f2 , e1 ,
  fst ec1 w (⊑-refl· w) (#SUP a1 f1) tt c1 ,
  snd ec1 w (⊑-refl· w) (#SUP a2 f2) tt c2 ,
  λ b1 b2 b∈ → →meq₀ kb i w eqa eqb (#APPLY f1 b1) (#APPLY f2 b2) (p b1 b2 b∈)
  where
    ec1 : NOREADeq w t u
    ec1 = kb (equalInTypeNOREAD→ ec) w (⊑-refl· w)


meq₀→ : (i : ℕ) (w : 𝕎·) (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t u : CTerm)
      → meq₀ eqa eqb w t u
      → meq eqa eqb (equalInType i w #NOREAD) w t u
meq.meqC (meq₀→ i w eqa eqb t u h) with meq₀.meqC₀ h
... | a1 , f1 , a2 , f2 , e1 , c1 , c2 , p =
  a1 , f1 , a2 , f2 , e1 ,
  lower (c1 w (⊑-refl· w)) , lower (c2 w (⊑-refl· w)) ,
  →equalInTypeNOREAD (Mod.∀𝕎-□ M (λ w1 e1 → #⇛→NOREADeq {w1} {t} {u} {#SUP a1 f1} {#SUP a2 f2} tt tt (∀𝕎-mon e1 c1) (∀𝕎-mon e1 c2))) ,
  λ b1 b2 b∈ → meq₀→ i w eqa eqb (#APPLY f1 b1) (#APPLY f2 b2) (p _ _ b∈)


abstract
  equalInType-W₀→ : (kb : K□) (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t₁ t₂ : CTerm)
                   → equalInType i w (#WT₀ A B) t₁ t₂
                   → □· w (λ w' _ → weq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t₁ t₂)
  equalInType-W₀→ kb i w A B t₁ t₂ eqi =
    Mod.∀𝕎-□Func M
      (λ w1 e1 h → →weq₀ kb i w1 (equalInType i w1 A) (λ a b eqa → equalInType i w1 (sub0 a B)) t₁ t₂ h)
      (equalInType-W→ i w A B #NOREAD t₁ t₂ eqi)


abstract
  →equalInType-W₀ : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                  → isType i w A
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
                  → □· w (λ w' _ → weq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t u)
                  → equalInType i w (#WT₀ A B) t u
  →equalInType-W₀ i w A B t u eqta eqtb h =
    →equalInType-W i w A B #NOREAD t u eqta eqtb eqTypesNOREAD
      (Mod.∀𝕎-□Func M (λ w1 e1 q → weq₀→ i w1 (equalInType i w1 A) (λ a b eqa → equalInType i w1 (sub0 a B)) t u q) h)


abstract
  equalInType-M₀→ : (kb : K□) (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t₁ t₂ : CTerm)
                   → equalInType i w (#MT₀ A B) t₁ t₂
                   → □· w (λ w' _ → meq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t₁ t₂)
  equalInType-M₀→ kb i w A B t₁ t₂ eqi =
    Mod.∀𝕎-□Func M
      (λ w1 e1 h → →meq₀ kb i w1 (equalInType i w1 A) (λ a b eqa → equalInType i w1 (sub0 a B)) t₁ t₂ h)
      (equalInType-M→ i w A B #NOREAD t₁ t₂ eqi)


abstract
  →equalInType-M₀ : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                  → isType i w A
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
                  → □· w (λ w' _ → meq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t u)
                  → equalInType i w (#MT₀ A B) t u
  →equalInType-M₀ i w A B t u eqta eqtb h =
    →equalInType-M i w A B #NOREAD t u eqta eqtb eqTypesNOREAD
      (Mod.∀𝕎-□Func M (λ w1 e1 q → meq₀→ i w1 (equalInType i w1 A) (λ a b eqa → equalInType i w1 (sub0 a B)) t u q) h)


abstract
  eqTypesW₀← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
            → equalTypes i w A C
            → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
            → equalTypes i w (#WT₀ A B) (#WT₀ C D)
  eqTypesW₀← {w} {i} {A} {B} {C} {D} eqta eqtb = eqTypesW← eqta eqtb eqTypesNOREAD

\end{code}
