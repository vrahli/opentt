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
open import terms6(W)(C)(M)(G)(E)(N)



#[2]CHOOSE : CTerm2 → CTerm2 → CTerm2
#[2]CHOOSE a b = ct2 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[2]APPLY : CTerm2 → CTerm2 → CTerm2
#[2]APPLY a b = ct2 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[1]NUM : ℕ → CTerm1
#[1]NUM n = ct1 (NUM n) refl


#[2]NUM : ℕ → CTerm2
#[2]NUM n = ct2 (NUM n) refl


#[0]BTRUE : CTerm0
#[0]BTRUE = ct0 BTRUE c
  where
    c : #[ [ 0 ] ] BTRUE
    c = refl


#[1]BTRUE : CTerm1
#[1]BTRUE = ct1 BTRUE c
  where
    c : #[ 0 ∷ [ 1 ] ] BTRUE
    c = refl


#[2]BTRUE : CTerm2
#[2]BTRUE = ct2 BTRUE c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] BTRUE
    c = refl


#[0]BFALSE : CTerm0
#[0]BFALSE = ct0 BFALSE c
  where
    c : #[ [ 0 ] ] BFALSE
    c = refl


#[1]BFALSE : CTerm1
#[1]BFALSE = ct1 BFALSE c
  where
    c : #[ 0 ∷ [ 1 ] ] BFALSE
    c = refl


#[2]BFALSE : CTerm2
#[2]BFALSE = ct2 BFALSE c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] BFALSE
    c = refl


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


#[0]set⊤ : Name → CTerm0
#[0]set⊤ r = #[0]CHOOSE (#[0]NAME r) #[0]BTRUE


#[1]set⊤ : Name → CTerm1
#[1]set⊤ r = #[1]CHOOSE (#[1]NAME r) #[1]BTRUE


#[2]set⊤ : Name → CTerm2
#[2]set⊤ r = #[2]CHOOSE (#[2]NAME r) #[2]BTRUE


#[0]set⊥ : Name → CTerm0
#[0]set⊥ r = #[0]CHOOSE (#[0]NAME r) #[0]BFALSE


#[1]set⊥ : Name → CTerm1
#[1]set⊥ r = #[1]CHOOSE (#[1]NAME r) #[1]BFALSE


#[2]set⊥ : Name → CTerm2
#[2]set⊥ r = #[2]CHOOSE (#[2]NAME r) #[2]BFALSE


#[0]get0 : Name → CTerm0
#[0]get0 name = #[0]APPLY (#[0]CS name) (#[0]NUM 0)


#[1]get0 : Name → CTerm1
#[1]get0 name = #[1]APPLY (#[1]CS name) (#[1]NUM 0)


#[2]get0 : Name → CTerm2
#[2]get0 name = #[2]APPLY (#[2]CS name) (#[2]NUM 0)


#[2]SEQ : CTerm2 → CTerm2 → CTerm2
#[2]SEQ a b = ct2 (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[0]PAIR : CTerm0 → CTerm0 → CTerm0
#[0]PAIR a b = ct0 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


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


#IFLT : CTerm → CTerm → CTerm → CTerm → CTerm
#IFLT a b c d = ct (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : # IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
            | CTerm.closed a
            | CTerm.closed b
            | CTerm.closed c
            | CTerm.closed d = refl


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


#[1]IFLT : CTerm1 → CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]IFLT a b c d = ct1 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ [ 1 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ [ 1 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm1.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm1.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm1.closed c)) (⊆?→⊆ (CTerm1.closed d)))))


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


#[0]SUP : CTerm0 → CTerm0 → CTerm0
#[0]SUP a b = ct0 (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] SUP ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


#[1]SUP : CTerm1 → CTerm1 → CTerm1
#[1]SUP a b = ct1 (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUP ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[2]SUP : CTerm2 → CTerm2 → CTerm2
#[2]SUP a b = ct2 (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SUP ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[3]SUP : CTerm3 → CTerm3 → CTerm3
#[3]SUP a b = ct3 (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] SUP ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


#[0]INL : CTerm0 → CTerm0
#[0]INL a = ct0 (INL ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] INL ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {[ 0 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))


#[1]INL : CTerm1 → CTerm1
#[1]INL a = ct1 (INL ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] INL ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ [ 1 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))


#[2]INL : CTerm2 → CTerm2
#[2]INL a = ct2 (INL ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] INL ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ [ 2 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))


#[3]INL : CTerm3 → CTerm3
#[3]INL a = ct3 (INL ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] INL ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[0]INR : CTerm0 → CTerm0
#[0]INR a = ct0 (INR ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] INR ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {[ 0 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))


#[1]INR : CTerm1 → CTerm1
#[1]INR a = ct1 (INR ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] INR ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ [ 1 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))


#[2]INR : CTerm2 → CTerm2
#[2]INR a = ct2 (INR ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] INR ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ [ 2 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))


#[3]INR : CTerm3 → CTerm3
#[3]INR a = ct3 (INR ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] INR ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[0]SUC : CTerm0 → CTerm0
#[0]SUC a = ct0 (SUC ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {[ 0 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))


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


lowerVars2-fvars-[0,1] : {l : List Var}
                              → l ⊆ (0 ∷ [ 1 ])
                              → lowerVars (lowerVars l) ≡ []
lowerVars2-fvars-[0,1] {[]} h = refl
lowerVars2-fvars-[0,1] {0 ∷ l} h = lowerVars2-fvars-[0,1] (λ z → h (there z))
lowerVars2-fvars-[0,1] {suc 0 ∷ l} h = lowerVars2-fvars-[0,1] (λ z → h (there z))
lowerVars2-fvars-[0,1] {suc (suc z) ∷ l} h = ⊥-elim (i w)
  where
    w : suc (suc z) ∈ (0 ∷ [ 1 ])
    w = h (here refl)

    i : suc (suc z) ∈ (0 ∷ [ 1 ]) → ⊥
    i (there (here px)) = suc-≢-0 (suc-injective px)


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


#SPREAD : CTerm → CTerm1 → CTerm
#SPREAD a b = ct (SPREAD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # SPREAD ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a = lowerVars2-fvars-[0,1] (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b))


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


#FST : CTerm → CTerm
#FST t = #SPREAD t #[1]VAR0


#SND : CTerm → CTerm
#SND t = #SPREAD t #[1]VAR1


#[0]FST : CTerm0 → CTerm0
#[0]FST t = #[0]SPREAD t #[2]VAR0


#[0]SND : CTerm0 → CTerm0
#[0]SND t = #[0]SPREAD t #[2]VAR1


#[1]FST : CTerm1 → CTerm1
#[1]FST t = #[1]SPREAD t #[3]VAR0


#[1]SND : CTerm1 → CTerm1
#[1]SND t = #[1]SPREAD t #[3]VAR1


#[2]FST : CTerm2 → CTerm2
#[2]FST t = #[2]SPREAD t #[4]VAR0


#[2]SND : CTerm2 → CTerm2
#[2]SND t = #[2]SPREAD t #[4]VAR1


#[3]FST : CTerm3 → CTerm3
#[3]FST t = #[3]SPREAD t #[5]VAR0


#[3]SND : CTerm3 → CTerm3
#[3]SND t = #[3]SPREAD t #[5]VAR1


⇓-FST-PAIR : (a b : Term) (w : 𝕎·) (ca : # a)
             → FST (PAIR a b) ⇓ a from w to w
⇓-FST-PAIR a b w ca = 1 , ≡pair e refl
  where
    e : sub b (sub a (VAR 0)) ≡ a
    e rewrite sub-VAR0 a | #subv 0 (shiftUp 0 b) a ca | #shiftDown 0 (ct a ca) = refl


⇛-FST-PAIR : (p a b : Term) (w : 𝕎·) (ca : # a)
              → p ⇛ PAIR a b at w
              → FST p ⇛ a at w
⇛-FST-PAIR p a b w ca c w1 e1 =
  lift (⇓-from-to→⇓
         {w1} {proj₁ c1} {FST p} {a}
         (⇓-trans₂ {w1} {proj₁ c1} {proj₁ c1} {FST p} {FST (PAIR a b)} {a} (snd c2) (⇓-FST-PAIR a b (proj₁ c1) ca)))
  where
    c1 : Σ 𝕎· (λ w2 → p ⇓ PAIR a b from w1 to w2)
    c1 = ⇓→from-to (lower (c w1 e1))

    c2 : Σ 𝕎· (λ w2 → FST p ⇓ FST (PAIR a b) from w1 to w2)
    c2 = fst c1 , SPREAD⇓₁ {w1} {proj₁ c1} {p} {PAIR a b} {VAR 0} (snd c1)


#⇛-FST-PAIR : (p a b : CTerm) (w : 𝕎·)
               → p #⇛ #PAIR a b at w
               → #FST p #⇛ a at w
#⇛-FST-PAIR p a b w c = ⇛-FST-PAIR ⌜ p ⌝ ⌜ a ⌝ ⌜ b ⌝ w (CTerm.closed a) c


sub-VAR1 : (a : Term) → sub a (VAR 1) ≡ VAR 0
sub-VAR1 a = refl


⇓-SND-PAIR : (a b : Term) (w : 𝕎·)
             → SND (PAIR a b) ⇓ b from w to w
⇓-SND-PAIR a b w = 1 , ≡pair e refl
  where
    e : sub b (sub a (VAR 1)) ≡ b
    e rewrite sub-VAR1 a | shiftDownUp b 0 = refl


⇛-SND-PAIR : (p a b : Term) (w : 𝕎·)
              → p ⇛ PAIR a b at w
              → SND p ⇛ b at w
⇛-SND-PAIR p a b w c w1 e1 =
  lift (⇓-from-to→⇓
         {w1} {fst c1} {SND p} {b}
         (⇓-trans₂ {w1} {fst c1} {fst c1} {SND p} {SND (PAIR a b)} {b} (snd c2) (⇓-SND-PAIR a b (fst c1))))
  where
    c1 : Σ 𝕎· (λ w2 → p ⇓ PAIR a b from w1 to w2)
    c1 = ⇓→from-to (lower (c w1 e1))

    c2 : Σ 𝕎· (λ w2 → SND p ⇓ SND (PAIR a b) from w1 to w2)
    c2 = fst c1 , SPREAD⇓₁ {w1} {fst c1} {p} {PAIR a b} {VAR 1} (snd c1)


#⇛-SND-PAIR : (p a b : CTerm) (w : 𝕎·)
               → p #⇛ #PAIR a b at w
               → #SND p #⇛ b at w
#⇛-SND-PAIR p a b w c = ⇛-SND-PAIR ⌜ p ⌝ ⌜ a ⌝ ⌜ b ⌝ w c


#⇛-trans : {w : 𝕎·} {a b c : CTerm} → a #⇛ b at w → b #⇛ c at w → a #⇛ c at w
#⇛-trans {w} {a} {b} {c} c₁ c₂ = ⇛-trans c₁ c₂


#⇛-FST-PAIR2 : (p a b c : CTerm) (w : 𝕎·)
                → p #⇛ #PAIR a b at w
                → a #⇛ c at w
                → #FST p #⇛ c at w
#⇛-FST-PAIR2 p a b c w c1 c2 = #⇛-trans {w} {#FST p} {a} {c} (#⇛-FST-PAIR p a b w c1) c2


#⇛-SND-PAIR2 : (p a b c : CTerm) (w : 𝕎·)
                → p #⇛ #PAIR a b at w
                → b #⇛ c at w
                → #SND p #⇛ c at w
#⇛-SND-PAIR2 p a b c w c1 c2 = #⇛-trans {w} {#SND p} {b} {c} (#⇛-SND-PAIR p a b w c1) c2


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


DECIDE-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t u : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (DECIDE a t u , w) ≡ (DECIDE b t u , w'))
DECIDE-steps₁ {0} {w} {w'} {a} {b} {t} {u} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
DECIDE-steps₁ {suc k} {w} {w'} {a} {b} {t} {u} comp with is-INL a
... | inj₁ (v , p) rewrite p | stepsVal (INL v) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with is-INR a
... |    inj₁ (v , p) rewrite p | stepsVal (INR v) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... |    inj₂ y with step⊎ a w
... |       inj₁ (z , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (DECIDE a t u , w) ≡ (DECIDE b t u , w'))
    c with is-INL a
    ... | inj₁ (u' , p') rewrite p' = ⊥-elim (x u' refl)
    ... | inj₂ x' with is-INR a
    ... |    inj₁ (u' , p') rewrite p' = ⊥-elim (y u' refl)
    ... |    inj₂ y' rewrite q = DECIDE-steps₁ {k} comp
... |       inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


DECIDE⇓₁ : {w w' : 𝕎·} {a b t u : Term}
         → a ⇓ b from w to w'
         → DECIDE a t u ⇓ DECIDE b t u from w to w'
DECIDE⇓₁ {w} {w'} {a} {b} {t} {u} (k , comp) = DECIDE-steps₁ {k} {w} {w'} {a} {b} {t} {u} comp


DECIDE⇛₁ : {w : 𝕎·} {a a' b c : Term}
           → a ⇛ a' at w
           → DECIDE a b c ⇛ DECIDE a' b c at w
DECIDE⇛₁ {w} {a} {a'} {b} {c} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst z} (DECIDE⇓₁ (snd z)))
  where
    z : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    z = ⇓→from-to (lower (comp w1 e1))


ITE⇓₁ : {w w' : 𝕎·} {a b t u : Term}
         → a ⇓ b from w to w'
         → ITE a t u ⇓ ITE b t u from w to w'
ITE⇓₁ {w} {w'} {a} {b} {t} {u} comp = DECIDE⇓₁ comp



#DECIDE : CTerm → CTerm0 → CTerm0 → CTerm
#DECIDE a b c = ct (DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : # DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b | lowerVars-fvars-CTerm0≡[] c = refl


#[0]VOID : CTerm0
#[0]VOID = ct0 VOID c
  where
    c : #[ [ 0 ] ] VOID
    c = refl


#VOID : CTerm
#VOID = ct VOID c
  where
    c : # VOID
    c = refl

\end{code}
