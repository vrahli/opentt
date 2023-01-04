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


module terms8 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)
open import terms2(W)(C)(M)(G)(E)(N)
open import terms3(W)(C)(M)(G)(E)(N)



#[2]CHOOSE : CTerm2 → CTerm2 → CTerm2
#[2]CHOOSE a b = ct2 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[2]SEQ : CTerm2 → CTerm2 → CTerm2
#[2]SEQ a b = ct2 (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[2]APPLY : CTerm2 → CTerm2 → CTerm2
#[2]APPLY a b = ct2 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[1]PAIR : CTerm1 → CTerm1 → CTerm1
#[1]PAIR a b = ct1 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[3]PAIR : CTerm3 → CTerm3 → CTerm3
#[3]PAIR a b = ct3 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


#[1]BTRUE : CTerm1
#[1]BTRUE = ct1 BTRUE c
  where
    c : #[ 0 ∷ [ 1 ] ] BTRUE
    c = refl


#[1]LET : CTerm1 → CTerm2 → CTerm1
#[1]LET a b = ct1 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#ITE : CTerm → CTerm → CTerm → CTerm
#ITE a b c = ct (ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : # ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d rewrite CTerm.closed a | #shiftUp 0 b | lowerVars-fvars-CTerm≡[] b | #shiftUp 0 c | lowerVars-fvars-CTerm≡[] c = refl


fvars-ITE0 : (a b c : Term) → fvars (ITE a b c) ≡ fvars a ++ fvars b ++ fvars c
fvars-ITE0 a b c
  rewrite fvars-shiftUp≡ 0 b
        | fvars-shiftUp≡ 0 c
        | lowerVars-map-sucIf≤-suc 0 (fvars b)
        | lowerVars-map-sucIf≤-suc 0 (fvars c)
        | loweVars-suc (fvars b)
        | loweVars-suc (fvars c) = refl


#[0]ITE : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]ITE a b c = ct0 (ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : #[ [ 0 ] ] ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d rewrite fvars-ITE0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {[ 0 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝}
            (⊆?→⊆ (CTerm0.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝} (⊆?→⊆ (CTerm0.closed b)) (⊆?→⊆ (CTerm0.closed c))))


#[2]ITE : CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]ITE a b c = ct2 (ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : #[ 0 ∷ 1 ∷ [ 2 ] ] ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d rewrite fvars-ITE0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ [ 2 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝}
            (⊆?→⊆ (CTerm2.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝} (⊆?→⊆ (CTerm2.closed b)) (⊆?→⊆ (CTerm2.closed c))))


fvars-IFLT0 : (a b c d : Term) → fvars (IFLT a b c d) ≡ fvars a ++ fvars b ++ fvars c ++ fvars d
fvars-IFLT0 a b c d
  rewrite fvars-shiftUp≡ 0 b
        | fvars-shiftUp≡ 0 c
        | fvars-shiftUp≡ 0 d
        | lowerVars-map-sucIf≤-suc 0 (fvars b)
        | lowerVars-map-sucIf≤-suc 0 (fvars c)
        | lowerVars-map-sucIf≤-suc 0 (fvars d)
        | loweVars-suc (fvars b)
        | loweVars-suc (fvars c)
        | loweVars-suc (fvars d) = refl


#[0]IFLT : CTerm0 → CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]IFLT a b c d = ct0 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ [ 0 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {[ 0 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm0.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm0.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm0.closed c)) (⊆?→⊆ (CTerm0.closed d)))))


#[2]IFLT : CTerm2 → CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]IFLT a b c d = ct2 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ [ 2 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ [ 2 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm2.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm2.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm2.closed c)) (⊆?→⊆ (CTerm2.closed d)))))


#[2]CS : Name → CTerm2
#[2]CS name = ct2 (CS name) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] CS name
    c = refl


#[2]NAME : Name → CTerm2
#[2]NAME name = ct2 (NAME name) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] NAME name
    c = refl


[0,1]⊆[0,1,2] : 0 ∷ [ 1 ] ⊆ (0 ∷ 1 ∷ [ 2 ])
[0,1]⊆[0,1,2] (here refl) = here refl
[0,1]⊆[0,1,2] (there (here refl)) = there (here refl)


[0,1,2]⊆[0,1,2,3] : 0 ∷ 1 ∷ [ 2 ] ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
[0,1,2]⊆[0,1,2,3] (here refl) = here refl
[0,1,2]⊆[0,1,2,3] (there (here refl)) = there (here refl)
[0,1,2]⊆[0,1,2,3] (there (there (here refl))) = there (there (here refl))


[0,1,2,3]⊆[0,1,2,3,4] : 0 ∷ 1 ∷ 2 ∷ [ 3 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
[0,1,2,3]⊆[0,1,2,3,4] (here refl) = here refl
[0,1,2,3]⊆[0,1,2,3,4] (there (here refl)) = there (here refl)
[0,1,2,3]⊆[0,1,2,3,4] (there (there (here refl))) = there (there (here refl))
[0,1,2,3]⊆[0,1,2,3,4] (there (there (there (here refl)))) = there (there (there (here refl)))


CTerm0→1 : CTerm0 → CTerm1
CTerm0→1 t = ct1 ⌜ t ⌝ c
  where
    c : #[ 0 ∷ [ 1 ] ] ⌜ t ⌝
    c = ⊆→⊆? {fvars ⌜ t ⌝} {0 ∷ [ 1 ]}
              (⊆-trans (⊆?→⊆ (CTerm0.closed t)) [0]⊆[0,1])


CTerm1→2 : CTerm1 → CTerm2
CTerm1→2 t = ct2 ⌜ t ⌝ c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] ⌜ t ⌝
    c = ⊆→⊆? {fvars ⌜ t ⌝} {0 ∷ 1 ∷ [ 2 ]}
              (⊆-trans (⊆?→⊆ (CTerm1.closed t)) [0,1]⊆[0,1,2])


CTerm2→3 : CTerm2 → CTerm3
CTerm2→3 t = ct3 ⌜ t ⌝ c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] ⌜ t ⌝
    c = ⊆→⊆? {fvars ⌜ t ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆-trans (⊆?→⊆ (CTerm2.closed t)) [0,1,2]⊆[0,1,2,3])



lowerVars-fvars-[0,1,2,3] : {l : List Var}
                            → l ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
                            → lowerVars l ⊆ 0 ∷ 1 ∷ [ 2 ]
lowerVars-fvars-[0,1,2,3] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ [ 3 ]) →  x₁ ∈ 0 ∷ 1 ∷ [ 2 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
lowerVars-fvars-[0,1,2,3] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3] (λ z → h (there z)) x



lowerVars-fvars-[0,1,2,3,4] : {l : List Var}
                            → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
                            → lowerVars l ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
lowerVars-fvars-[0,1,2,3,4] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3,4] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3,4] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]) →  x₁ ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
    i (there (there (there (there (here px))))) = there (there (there (here (suc-injective px))))
lowerVars-fvars-[0,1,2,3,4] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3,4] (λ z → h (there z)) x


#[2]LAMBDA : CTerm3 → CTerm2
#[2]LAMBDA b = ct2 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ [ 2 ]}
              (lowerVars-fvars-[0,1,2,3] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm3.closed b)))


#[1]SUP : CTerm1 → CTerm1 → CTerm1
#[1]SUP a b = ct1 (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUP ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[3]SUP : CTerm3 → CTerm3 → CTerm3
#[3]SUP a b = ct3 (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] SUP ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


#[1]INL : CTerm1 → CTerm1
#[1]INL a = ct1 (INL ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] INL ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ [ 1 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))


#[3]INL : CTerm3 → CTerm3
#[3]INL a = ct3 (INL ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] INL ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[1]INR : CTerm1 → CTerm1
#[1]INR a = ct1 (INR ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] INR ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ [ 1 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))


#[3]INR : CTerm3 → CTerm3
#[3]INR a = ct3 (INR ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] INR ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[1]SUC : CTerm1 → CTerm1
#[1]SUC a = ct1 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ [ 1 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))


#[3]SUC : CTerm3 → CTerm3
#[3]SUC a = ct3 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[0]AX : CTerm0
#[0]AX = ct0 AX c
  where
    c : #[ [ 0 ] ] AX
    c = refl


#[1]AX : CTerm1
#[1]AX = ct1 AX c
  where
    c : #[ 0 ∷ [ 1 ] ] AX
    c = refl


#[2]AX : CTerm2
#[2]AX = ct2 AX c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] AX
    c = refl


#[3]AX : CTerm3
#[3]AX = ct3 AX c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] AX
    c = refl


[0]⊆[0,1,2] : [ 0 ] ⊆ (0 ∷ 1 ∷ [ 2 ])
[0]⊆[0,1,2] (here px) rewrite px = here refl


[1]⊆[0,1,2] : [ 1 ] ⊆ (0 ∷ 1 ∷ [ 2 ])
[1]⊆[0,1,2] (here px) rewrite px = there (here refl)


[0]⊆[0,1,2,3] : [ 0 ] ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
[0]⊆[0,1,2,3] (here refl) = here refl


[1]⊆[0,1,2,3] : [ 1 ] ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
[1]⊆[0,1,2,3] (here refl) = there (here refl)


[2]⊆[0,1,2,3] : [ 2 ] ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
[2]⊆[0,1,2,3] (here refl) = there (there (here refl))


[3]⊆[0,1,2,3] : [ 3 ] ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
[3]⊆[0,1,2,3] (here refl) = there (there (there (here refl)))


[0]⊆[0,1,2,3,4] : [ 0 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
[0]⊆[0,1,2,3,4] (here refl) = here refl


[1]⊆[0,1,2,3,4] : [ 1 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
[1]⊆[0,1,2,3,4] (here refl) = there (here refl)


[0]⊆[0,1,2,3,4,5] : [ 0 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[0]⊆[0,1,2,3,4,5] (here refl) = here refl


[1]⊆[0,1,2,3,4,5] : [ 1 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[1]⊆[0,1,2,3,4,5] (here refl) = there (here refl)


#[2]VAR0 : CTerm2
#[2]VAR0 = ct2 (VAR 0) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1,2]


#[2]VAR1 : CTerm2
#[2]VAR1 = ct2 (VAR 1) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1,2]


#[3]VAR0 : CTerm3
#[3]VAR0 = ct3 (VAR 0) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1,2,3]


#[3]VAR1 : CTerm3
#[3]VAR1 = ct3 (VAR 1) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1,2,3]


#[3]VAR2 : CTerm3
#[3]VAR2 = ct3 (VAR 2) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] VAR 2
    c = ⊆→⊆? [2]⊆[0,1,2,3]


#[3]VAR3 : CTerm3
#[3]VAR3 = ct3 (VAR 3) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] VAR 3
    c = ⊆→⊆? [3]⊆[0,1,2,3]


#[3]APPLY : CTerm3 → CTerm3 → CTerm3
#[3]APPLY a b = ct3 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


record CTerm4 : Set where
  constructor ct4
  field
    cTerm  : Term
    closed : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] cTerm


instance
  CTerm4ToTerm : ToTerm CTerm4
  ⌜_⌝ {{CTerm4ToTerm}} t = CTerm4.cTerm t


CTerm→CTerm4 : CTerm → CTerm4
CTerm→CTerm4 (ct t c) = ct4 t c'
  where
    c' : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm4 : fromCTerm CTerm4
  ⌞_⌟ {{CTermToCTerm4}} t = CTerm→CTerm4 t


#[4]VAR0 : CTerm4
#[4]VAR0 = ct4 (VAR 0) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1,2,3,4]


#[4]VAR1 : CTerm4
#[4]VAR1 = ct4 (VAR 1) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1,2,3,4]


record CTerm5 : Set where
  constructor ct5
  field
    cTerm  : Term
    closed : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] cTerm


instance
  CTerm5ToTerm : ToTerm CTerm5
  ⌜_⌝ {{CTerm5ToTerm}} t = CTerm5.cTerm t


CTerm→CTerm5 : CTerm → CTerm5
CTerm→CTerm5 (ct t c) = ct5 t c'
  where
    c' : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm5 : fromCTerm CTerm5
  ⌞_⌟ {{CTermToCTerm5}} t = CTerm→CTerm5 t


#[5]VAR0 : CTerm5
#[5]VAR0 = ct5 (VAR 0) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1,2,3,4,5]


#[5]VAR1 : CTerm5
#[5]VAR1 = ct5 (VAR 1) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1,2,3,4,5]


lowerVars2-fvars-[0,1,2] : {l : List Var}
                              → l ⊆ (0 ∷ 1 ∷ [ 2 ])
                              → lowerVars (lowerVars l) ⊆ [ 0 ]
lowerVars2-fvars-[0,1,2] {0 ∷ l} h x = lowerVars2-fvars-[0,1,2] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2] {suc 0 ∷ l} h x = lowerVars2-fvars-[0,1,2] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2] {suc (suc z) ∷ l} h (here px) rewrite px = i w
  where
    w : suc (suc z) ∈ (0 ∷ 1 ∷ [ 2 ])
    w = h (here refl)

    i : suc (suc z) ∈ (0 ∷ 1 ∷ [ 2 ]) →  z ∈ [ 0 ]
    i (there (there (here q))) = here (suc-injective (suc-injective q)) --
lowerVars2-fvars-[0,1,2] {suc (suc z) ∷ l} h (there x) = lowerVars2-fvars-[0,1,2] (λ z → h (there z)) x


lowerVars2-fvars-[0,1,2,3] : {l : List Var}
                              → l ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
                              → lowerVars (lowerVars l) ⊆ 0 ∷ [ 1 ]
lowerVars2-fvars-[0,1,2,3] {0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3] {suc 0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3] {suc (suc z) ∷ l} h (here px) rewrite px = i w
  where
    w : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
    w = h (here refl)

    i : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ [ 3 ]) →  z ∈ 0 ∷ [ 1 ]
    i (there (there (here q))) = here (suc-injective (suc-injective q)) --
    i (there (there (there (here q)))) = there (here (suc-injective (suc-injective q)))
lowerVars2-fvars-[0,1,2,3] {suc (suc z) ∷ l} h (there x) = lowerVars2-fvars-[0,1,2,3] (λ z → h (there z)) x


lowerVars2-fvars-[0,1,2,3,4] : {l : List Var}
                              → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
                              → lowerVars (lowerVars l) ⊆ 0 ∷ 1 ∷ [ 2 ]
lowerVars2-fvars-[0,1,2,3,4] {0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3,4] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3,4] {suc 0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3,4] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3,4] {suc (suc z) ∷ l} h (here px) rewrite px = i w
  where
    w : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
    w = h (here refl)

    i : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]) →  z ∈ 0 ∷ 1 ∷ [ 2 ]
    i (there (there (here q))) = here (suc-injective (suc-injective q)) --
    i (there (there (there (here q)))) = there (here (suc-injective (suc-injective q)))
    i (there (there (there (there (here q))))) = there (there (here (suc-injective (suc-injective q))))
lowerVars2-fvars-[0,1,2,3,4] {suc (suc z) ∷ l} h (there x) = lowerVars2-fvars-[0,1,2,3,4] (λ z → h (there z)) x


lowerVars2-fvars-[0,1,2,3,4,5] : {l : List Var}
                              → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
                              → lowerVars (lowerVars l) ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
lowerVars2-fvars-[0,1,2,3,4,5] {0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3,4,5] {suc 0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3,4,5] {suc (suc z) ∷ l} h (here px) rewrite px = i w
  where
    w : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
    w = h (here refl)

    i : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]) →  z ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
    i (there (there (here q))) = here (suc-injective (suc-injective q)) --
    i (there (there (there (here q)))) = there (here (suc-injective (suc-injective q)))
    i (there (there (there (there (here q))))) = there (there (here (suc-injective (suc-injective q))))
    i (there (there (there (there (there (here q)))))) = there (there (there (here (suc-injective (suc-injective q)))))
lowerVars2-fvars-[0,1,2,3,4,5] {suc (suc z) ∷ l} h (there x) = lowerVars2-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x


#[0]SPREAD : CTerm0 → CTerm2 → CTerm0
#[0]SPREAD a b = ct0 (SPREAD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] SPREAD ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (lowerVars (fvars ⌜ b ⌝))} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars2-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[1]SPREAD : CTerm1 → CTerm3 → CTerm1
#[1]SPREAD a b = ct1 (SPREAD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SPREAD ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (lowerVars (fvars ⌜ b ⌝))} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars2-fvars-[0,1,2,3] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm3.closed b))))


#[2]SPREAD : CTerm2 → CTerm4 → CTerm2
#[2]SPREAD a b = ct2 (SPREAD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SPREAD ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (lowerVars (fvars ⌜ b ⌝))} {0 ∷ 1 ∷ [ 2 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                   (lowerVars2-fvars-[0,1,2,3,4] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm4.closed b))))


#[3]SPREAD : CTerm3 → CTerm5 → CTerm3
#[3]SPREAD a b = ct3 (SPREAD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] SPREAD ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (lowerVars (fvars ⌜ b ⌝))} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                   (lowerVars2-fvars-[0,1,2,3,4,5] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm5.closed b))))


#[0]FST : CTerm0 → CTerm0
#[0]FST t = #[0]SPREAD t #[2]VAR1


#[0]SND : CTerm0 → CTerm0
#[0]SND t = #[0]SPREAD t #[2]VAR0


#[1]FST : CTerm1 → CTerm1
#[1]FST t = #[1]SPREAD t #[3]VAR1


#[1]SND : CTerm1 → CTerm1
#[1]SND t = #[1]SPREAD t #[3]VAR0


#[2]FST : CTerm2 → CTerm2
#[2]FST t = #[2]SPREAD t #[4]VAR1


#[2]SND : CTerm2 → CTerm2
#[2]SND t = #[2]SPREAD t #[4]VAR0


#[3]FST : CTerm3 → CTerm3
#[3]FST t = #[3]SPREAD t #[5]VAR1


#[3]SND : CTerm3 → CTerm3
#[3]SND t = #[3]SPREAD t #[5]VAR0


#[0]BFALSE : CTerm0
#[0]BFALSE = ct0 BFALSE c
  where
    c : #[ [ 0 ] ] BFALSE
    c = refl


#[2]BFALSE : CTerm2
#[2]BFALSE = ct2 BFALSE c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] BFALSE
    c = refl


#[3]LAMBDA : CTerm4 → CTerm3
#[3]LAMBDA b = ct3 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (lowerVars-fvars-[0,1,2,3,4] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm4.closed b)))


#[4]IFLT : CTerm4 → CTerm4 → CTerm4 → CTerm4 → CTerm4
#[4]IFLT a b c d = ct4 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm4.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm4.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm4.closed c)) (⊆?→⊆ (CTerm4.closed d)))))


#[4]APPLY : CTerm4 → CTerm4 → CTerm4
#[4]APPLY a b = ct4 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed b)))


CTerm3→4 : CTerm3 → CTerm4
CTerm3→4 t = ct4 ⌜ t ⌝ c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] ⌜ t ⌝
    c = ⊆→⊆? {fvars ⌜ t ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
              (⊆-trans (⊆?→⊆ (CTerm3.closed t)) [0,1,2,3]⊆[0,1,2,3,4])


#[0]shiftUp0 : CTerm → CTerm0
#[0]shiftUp0 t = ct0 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0 ⌜ t ⌝ | CTerm.closed t = refl


#[1]shiftUp0 : CTerm0 → CTerm1
#[1]shiftUp0 t = ct1 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ [ 1 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm0.cTerm t)) ⊆ 0 ∷ [ 1 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ≡ 0
            w = ∈[1] {Var} {y} {0} (⊆?→⊆ (CTerm0.closed t) {y} j)

            k : x ∈ 0 ∷ [ 1 ]
            k rewrite e | sym (suc≡sucIf≤0 y) | w = there (here refl)


#[2]shiftUp0 : CTerm1 → CTerm2
#[2]shiftUp0 t = ct2 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ 1 ∷ [ 2 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm1.cTerm t)) ⊆ 0 ∷ 1 ∷ [ 2 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ∈ 0 ∷ [ 1 ]
            w = ⊆?→⊆ (CTerm1.closed t) {y} j

            z : y ∈ 0 ∷ [ 1 ] → suc y ∈ 0 ∷ 1 ∷ [ 2 ]
            z (here px) rewrite px = there (here refl)
            z (there (here px)) rewrite px = there (there (here refl))

            k : x ∈ 0 ∷ 1 ∷ [ 2 ]
            k rewrite e | sym (suc≡sucIf≤0 y) = z w


#[3]shiftUp0 : CTerm2 → CTerm3
#[3]shiftUp0 t = ct3 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm2.cTerm t)) ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ∈ 0 ∷ 1 ∷ [ 2 ]
            w = ⊆?→⊆ (CTerm2.closed t) {y} j

            z : y ∈ 0 ∷ 1 ∷ [ 2 ] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
            z (here px) rewrite px = there (here refl)
            z (there (here px)) rewrite px = there (there (here refl))
            z (there (there (here px))) rewrite px = there (there (there (here refl)))

            k : x ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
            k rewrite e | sym (suc≡sucIf≤0 y) = z w


#[4]shiftUp0 : CTerm3 → CTerm4
#[4]shiftUp0 t = ct4 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm3.cTerm t)) ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
            w = ⊆?→⊆ (CTerm3.closed t) {y} j

            z : y ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
            z (here px) rewrite px = there (here refl)
            z (there (here px)) rewrite px = there (there (here refl))
            z (there (there (here px))) rewrite px = there (there (there (here refl)))
            z (there (there (there (here px)))) rewrite px = there (there (there (there (here refl))))

            k : x ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
            k rewrite e | sym (suc≡sucIf≤0 y) = z w

\end{code}
