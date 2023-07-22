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


module terms9 where



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





NAT!→U : ℕ → Term
NAT!→U i = FUN NAT! (UNIV i)


#NAT!→U : ℕ → CTerm
#NAT!→U i = ct (NAT!→U i) refl


#NAT!→U≡ : (i : ℕ) → #NAT!→U i ≡ #FUN #NAT! (#UNIV i)
#NAT!→U≡ i = CTerm≡ refl


#[0]LIFT : CTerm0 → CTerm0
#[0]LIFT a = ct0 (LIFT ⌜ a ⌝) (CTerm0.closed a)


#[1]LIFT : CTerm1 → CTerm1
#[1]LIFT a = ct1 (LIFT ⌜ a ⌝) (CTerm1.closed a)


#[2]LIFT : CTerm2 → CTerm2
#[2]LIFT a = ct2 (LIFT ⌜ a ⌝) (CTerm2.closed a)


fvars-CTerm1 : (a : CTerm1) → fvars ⌜ a ⌝ ⊆ 0 ∷ [ 1 ]
fvars-CTerm1 a = ⊆?→⊆ (CTerm1.closed a)


fvars-CTerm2 : (a : CTerm2) → fvars ⌜ a ⌝ ⊆ 0 ∷ 1 ∷ [ 2 ]
fvars-CTerm2 a = ⊆?→⊆ (CTerm2.closed a)


#[1]SQUASH : CTerm1 → CTerm1
#[1]SQUASH a = ct1 (SQUASH ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SQUASH ⌜ a ⌝
    c rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ = ⊆→⊆? {lowerVars (Data.List.map suc (fvars ⌜ a ⌝))} {0 ∷ [ 1 ]} s
      where
        s : lowerVars (Data.List.map suc (fvars ⌜ a ⌝)) ⊆ 0 ∷ [ 1 ]
        s {z} i = w
          where
            x : suc z ∈ Data.List.map suc (fvars ⌜ a ⌝)
            x = ∈lowerVars→ z (Data.List.map suc (fvars ⌜ a ⌝)) i

            y : Var
            y = fst (∈-map⁻ suc x)

            j : y ∈ fvars ⌜ a ⌝
            j = fst (snd (∈-map⁻ suc x))

            e : z ≡ y
            e = suc-injective (snd (snd (∈-map⁻ suc x)))

            w : z ∈ 0 ∷ [ 1 ]
            w rewrite e = fvars-CTerm1 a j


#[2]SQUASH : CTerm2 → CTerm2
#[2]SQUASH a = ct2 (SQUASH ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SQUASH ⌜ a ⌝
    c rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ = ⊆→⊆? {lowerVars (Data.List.map suc (fvars ⌜ a ⌝))} {0 ∷ 1 ∷ [ 2 ]} s
      where
        s : lowerVars (Data.List.map suc (fvars ⌜ a ⌝)) ⊆ 0 ∷ 1 ∷ [ 2 ]
        s {z} i = w
          where
            x : suc z ∈ Data.List.map suc (fvars ⌜ a ⌝)
            x = ∈lowerVars→ z (Data.List.map suc (fvars ⌜ a ⌝)) i

            y : Var
            y = fst (∈-map⁻ suc x)

            j : y ∈ fvars ⌜ a ⌝
            j = fst (snd (∈-map⁻ suc x))

            e : z ≡ y
            e = suc-injective (snd (snd (∈-map⁻ suc x)))

            w : z ∈ 0 ∷ 1 ∷ [ 2 ]
            w rewrite e = fvars-CTerm2 a j


#[1]UNION : CTerm1 → CTerm1 → CTerm1
#[1]UNION a b = ct1 (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] UNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


↑APPLY : Term → Term → Term
↑APPLY f a = LIFT (APPLY f a)


#↑APPLY : CTerm → CTerm → CTerm
#↑APPLY f a = #LIFT (#APPLY f a)


#[0]↑APPLY : CTerm0 → CTerm0 → CTerm0
#[0]↑APPLY f a = #[0]LIFT (#[0]APPLY f a)


#[1]↑APPLY : CTerm1 → CTerm1 → CTerm1
#[1]↑APPLY f a = #[1]LIFT (#[1]APPLY f a)


OR : Term → Term → Term
OR a b = SQUASH (UNION a b)


#OR : CTerm → CTerm → CTerm
#OR a b = #SQUASH (#UNION a b)


#[0]OR : CTerm0 → CTerm0 → CTerm0
#[0]OR a b = #[0]SQUASH (#[0]UNION a b)


#[1]OR : CTerm1 → CTerm1 → CTerm1
#[1]OR a b = #[1]SQUASH (#[1]UNION a b)



#[1]SUM : CTerm1 → CTerm2 → CTerm1
#[1]SUM a b = ct1 (SUM ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUM ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[1]PI : CTerm1 → CTerm2 → CTerm1
#[1]PI a b = ct1 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                      (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[3]EQ : CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]EQ a b c = ct3 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
                 (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                       (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b))
                             (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed c))))


#[1]BOOL : CTerm1
#[1]BOOL = ct1 BOOL refl


#[2]BOOL : CTerm2
#[2]BOOL = ct2 BOOL refl


#[3]BOOL : CTerm3
#[3]BOOL = ct3 BOOL refl


#[3]FUN : CTerm3 → CTerm3 → CTerm3
#[3]FUN a b = ct3 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                     (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))

\end{code}
