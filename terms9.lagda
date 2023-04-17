\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; _<?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Bool.Properties using ()
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

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import choiceExt
open import newChoice
open import encode


module terms9 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
              (EC : Encode)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)

open import computation(W)(C)(M)(G)(E)(N)(EC)
open import terms2(W)(C)(M)(G)(E)(N)(EC)
open import terms3(W)(C)(M)(G)(E)(N)(EC)
open import terms6(W)(C)(M)(G)(E)(N)(EC)



BAIRE! : Term
BAIRE! = FUN NAT NAT!


#BAIRE! : CTerm
#BAIRE! = ct BAIRE! c
  where
    c : # BAIRE!
    c = refl



-- MOVE to terms
BAIRE!→NAT : Term
BAIRE!→NAT = FUN BAIRE! NAT


-- MOVE to terms
#BAIRE!→NAT : CTerm
#BAIRE!→NAT = ct BAIRE!→NAT c
  where
    c : # BAIRE!→NAT
    c = refl


-- MOVE to terms
#BAIRE!→NAT≡ : #BAIRE!→NAT ≡ #FUN #BAIRE! #NAT
#BAIRE!→NAT≡ = CTerm≡ refl



#[0]BAIRE! : CTerm0
#[0]BAIRE! = ct0 BAIRE! c
  where
    c : #[ [ 0 ] ] BAIRE!
    c = refl


#[1]BAIRE! : CTerm1
#[1]BAIRE! = ct1 BAIRE! c
  where
    c : #[ 0 ∷ [ 1 ] ] BAIRE!
    c = refl


QNATn : Term → Term
QNATn n = SET NAT (QLT (VAR 0) (shiftUp 0 n))


QBAIREn : Term → Term
QBAIREn n = FUN (QNATn n) NAT


QBAIREn! : Term → Term
QBAIREn! n = FUN (QNATn n) NAT!


#QBAIREn! : CTerm → CTerm
#QBAIREn! n = ct (QBAIREn! ⌜ n ⌝) c
  where
    c : # QBAIREn! ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n


#QNATn : CTerm → CTerm
#QNATn n = ct (QNATn ⌜ n ⌝) c
  where
    c : # QNATn ⌜ n ⌝
    c rewrite ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n


≡QBAIREn! : (n : CTerm) → #QBAIREn! n ≡ #FUN (#QNATn n) #NAT!
≡QBAIREn! n = CTerm≡ refl



#[1]QBAIREn : CTerm1 → CTerm1
#[1]QBAIREn n = ct1 (QBAIREn ⌜ n ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] QBAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝))) =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {0 ∷ [ 1 ]}
           (lowerVars-fvars-[0,1,2] {fvars (shiftUp 0 ⌜ n ⌝)} (→fvars-shiftUp⊆-[0,1,2] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {0 ∷ [ 1 ]} (CTerm1.closed n))))



#[1]QBAIREn! : CTerm1 → CTerm1
#[1]QBAIREn! n = ct1 (QBAIREn! ⌜ n ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] QBAIREn! ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝))) =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {0 ∷ [ 1 ]}
           (lowerVars-fvars-[0,1,2] {fvars (shiftUp 0 ⌜ n ⌝)} (→fvars-shiftUp⊆-[0,1,2] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {0 ∷ [ 1 ]} (CTerm1.closed n))))



#[0]QBAIREn : CTerm0 → CTerm0
#[0]QBAIREn n = ct0 (QBAIREn ⌜ n ⌝) c
  where
    c : #[ [ 0 ] ] QBAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | lowerVars-fvars-CTerm0≡[] n =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {[ 0 ]}
            (lowerVars-fvars-[0,1] {fvars (shiftUp 0 ⌜ n ⌝)}
                                   (→fvars-shiftUp⊆-[0,1] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {[ 0 ]} (CTerm0.closed n))))


#[0]QBAIREn! : CTerm0 → CTerm0
#[0]QBAIREn! n = ct0 (QBAIREn! ⌜ n ⌝) c
  where
    c : #[ [ 0 ] ] QBAIREn! ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT!
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | lowerVars-fvars-CTerm0≡[] n =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {[ 0 ]}
            (lowerVars-fvars-[0,1] {fvars (shiftUp 0 ⌜ n ⌝)}
                                   (→fvars-shiftUp⊆-[0,1] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {[ 0 ]} (CTerm0.closed n))))


#QBAIREn : CTerm → CTerm
#QBAIREn n = ct (QBAIREn ⌜ n ⌝) c
  where
    c : # QBAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n


≡QBAIREn : (n : CTerm) → #QBAIREn n ≡ #FUN (#QNATn n) #NAT
≡QBAIREn n = CTerm≡ refl

\end{code}
