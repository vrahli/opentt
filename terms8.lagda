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


record CTerm6 : Set where
  constructor ct6
  field
    cTerm  : Term
    closed : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] cTerm


instance
  CTerm6ToTerm : ToTerm CTerm6
  ⌜_⌝ {{CTerm6ToTerm}} t = CTerm6.cTerm t


CTerm→CTerm6 : CTerm → CTerm6
CTerm→CTerm6 (ct t c) = ct6 t c'
  where
    c' : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm6 : fromCTerm CTerm6
  ⌞_⌟ {{CTermToCTerm6}} t = CTerm→CTerm6 t


record CTerm7 : Set where
  constructor ct7
  field
    cTerm  : Term
    closed : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] cTerm


instance
  CTerm7ToTerm : ToTerm CTerm7
  ⌜_⌝ {{CTerm7ToTerm}} t = CTerm7.cTerm t


CTerm→CTerm7 : CTerm → CTerm7
CTerm→CTerm7 (ct t c) = ct7 t c'
  where
    c' : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm7 : fromCTerm CTerm7
  ⌞_⌟ {{CTermToCTerm7}} t = CTerm→CTerm7 t


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


#[3]NUM : ℕ → CTerm3
#[3]NUM n = ct3 (NUM n) refl


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


#[3]CS : Name → CTerm3
#[3]CS name = ct3 (CS name) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] CS name
    c = refl


#[2]NAME : Name → CTerm2
#[2]NAME name = ct2 (NAME name) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] NAME name
    c = refl


#[1]NAT! : CTerm1
#[1]NAT! = ct1 NAT! refl


#[3]APPLY : CTerm3 → CTerm3 → CTerm3
#[3]APPLY a b = ct3 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


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


#[3]get0 : Name → CTerm3
#[3]get0 name = #[3]APPLY (#[3]CS name) (#[3]NUM 0)


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


#[2]PAIR : CTerm2 → CTerm2 → CTerm2
#[2]PAIR a b = ct2 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[3]PAIR : CTerm3 → CTerm3 → CTerm3
#[3]PAIR a b = ct3 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


#[4]PAIR : CTerm4 → CTerm4 → CTerm4
#[4]PAIR a b = ct4 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed b)))


#[5]PAIR : CTerm5 → CTerm5 → CTerm5
#[5]PAIR a b = ct5 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} (CTerm5.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} (CTerm5.closed b)))


#[6]PAIR : CTerm6 → CTerm6 → CTerm6
#[6]PAIR a b = ct6 (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] PAIR ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]} (CTerm6.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]} (CTerm6.closed b)))


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


fvars-IFEQ0 : (a b c d : Term) → fvars (IFEQ a b c d) ≡ fvars a ++ fvars b ++ fvars c ++ fvars d
fvars-IFEQ0 a b c d
  rewrite fvars-shiftUp≡ 0 b
        | fvars-shiftUp≡ 0 c
        | fvars-shiftUp≡ 0 d
        | lowerVars-map-sucIf≤-suc 0 (fvars b)
        | lowerVars-map-sucIf≤-suc 0 (fvars c)
        | lowerVars-map-sucIf≤-suc 0 (fvars d)
        | loweVars-suc (fvars b)
        | loweVars-suc (fvars c)
        | loweVars-suc (fvars d) = refl


#IFEQ : CTerm → CTerm → CTerm → CTerm → CTerm
#IFEQ a b c d = ct (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : # IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
            | CTerm.closed a
            | CTerm.closed b
            | CTerm.closed c
            | CTerm.closed d = refl


#[0]IFEQ : CTerm0 → CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]IFEQ a b c d = ct0 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ [ 0 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {[ 0 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm0.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm0.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm0.closed c)) (⊆?→⊆ (CTerm0.closed d)))))


#[1]IFEQ : CTerm1 → CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]IFEQ a b c d = ct1 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ [ 1 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ [ 1 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm1.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm1.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm1.closed c)) (⊆?→⊆ (CTerm1.closed d)))))


#[2]IFEQ : CTerm2 → CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]IFEQ a b c d = ct2 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ [ 2 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
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



lowerVars-fvars-[0,1,2,3,4,5] : {l : List Var}
                                → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
                                → lowerVars l ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
lowerVars-fvars-[0,1,2,3,4,5] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3,4,5] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]) →  x₁ ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
    i (there (there (there (there (here px))))) = there (there (there (here (suc-injective px))))
    i (there (there (there (there (there (here px)))))) = there (there (there (there (here (suc-injective px)))))
lowerVars-fvars-[0,1,2,3,4,5] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x



lowerVars-fvars-[0,1,2,3,4,5,6] : {l : List Var}
                                  → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
                                  → lowerVars l ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
lowerVars-fvars-[0,1,2,3,4,5,6] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3,4,5,6] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3,4,5,6] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]) →  x₁ ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
    i (there (there (there (there (here px))))) = there (there (there (here (suc-injective px))))
    i (there (there (there (there (there (here px)))))) = there (there (there (there (here (suc-injective px)))))
    i (there (there (there (there (there (there (here px))))))) = there (there (there (there (there (here (suc-injective px))))))
lowerVars-fvars-[0,1,2,3,4,5,6] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3,4,5,6] (λ z → h (there z)) x



lowerVars-fvars-[0,1,2,3,4,5,6,7] : {l : List Var}
                                  → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ])
                                  → lowerVars l ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]
lowerVars-fvars-[0,1,2,3,4,5,6,7] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3,4,5,6,7] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3,4,5,6,7] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]) →  x₁ ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
    i (there (there (there (there (here px))))) = there (there (there (here (suc-injective px))))
    i (there (there (there (there (there (here px)))))) = there (there (there (there (here (suc-injective px)))))
    i (there (there (there (there (there (there (here px))))))) = there (there (there (there (there (here (suc-injective px))))))
    i (there (there (there (there (there (there (there (here px)))))))) = there (there (there (there (there (there (here (suc-injective px)))))))
lowerVars-fvars-[0,1,2,3,4,5,6,7] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3,4,5,6,7] (λ z → h (there z)) x


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


#[2]SUC : CTerm2 → CTerm2
#[2]SUC a = ct2 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ [ 2 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))


#[3]SUC : CTerm3 → CTerm3
#[3]SUC a = ct3 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[4]SUC : CTerm4 → CTerm4
#[4]SUC a = ct4 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed a))


#[5]SUC : CTerm5 → CTerm5
#[5]SUC a = ct5 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} (CTerm5.closed a))


#[6]SUC : CTerm6 → CTerm6
#[6]SUC a = ct6 (SUC ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] SUC ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]} (CTerm6.closed a))


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


[2]⊆[0,1,2] : [ 2 ] ⊆ (0 ∷ 1 ∷ [ 2 ])
[2]⊆[0,1,2] (here px) rewrite px = there (there (here refl))


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


[2]⊆[0,1,2,3,4] : [ 2 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
[2]⊆[0,1,2,3,4] (here refl) = there (there (here refl))


[3]⊆[0,1,2,3,4] : [ 3 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
[3]⊆[0,1,2,3,4] (here refl) = there (there (there (here refl)))


[4]⊆[0,1,2,3,4] : [ 4 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
[4]⊆[0,1,2,3,4] (here refl) = there (there (there (there (here refl))))


[0]⊆[0,1,2,3,4,5] : [ 0 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[0]⊆[0,1,2,3,4,5] (here refl) = here refl


[1]⊆[0,1,2,3,4,5] : [ 1 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[1]⊆[0,1,2,3,4,5] (here refl) = there (here refl)


[2]⊆[0,1,2,3,4,5] : [ 2 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[2]⊆[0,1,2,3,4,5] (here refl) = there (there (here refl))


[3]⊆[0,1,2,3,4,5] : [ 3 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[3]⊆[0,1,2,3,4,5] (here refl) = there (there (there (here refl)))


[4]⊆[0,1,2,3,4,5] : [ 4 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[4]⊆[0,1,2,3,4,5] (here refl) = there (there (there (there (here refl))))


[5]⊆[0,1,2,3,4,5] : [ 5 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
[5]⊆[0,1,2,3,4,5] (here refl) = there (there (there (there (there (here refl)))))


[0]⊆[0,1,2,3,4,5,6] : [ 0 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[0]⊆[0,1,2,3,4,5,6] (here refl) = here refl


[1]⊆[0,1,2,3,4,5,6] : [ 1 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[1]⊆[0,1,2,3,4,5,6] (here refl) = there (here refl)


[2]⊆[0,1,2,3,4,5,6] : [ 2 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[2]⊆[0,1,2,3,4,5,6] (here refl) = there (there (here refl))


[3]⊆[0,1,2,3,4,5,6] : [ 3 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[3]⊆[0,1,2,3,4,5,6] (here refl) = there (there (there (here refl)))


[4]⊆[0,1,2,3,4,5,6] : [ 4 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[4]⊆[0,1,2,3,4,5,6] (here refl) = there (there (there (there (here refl))))


[5]⊆[0,1,2,3,4,5,6] : [ 5 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[5]⊆[0,1,2,3,4,5,6] (here refl) = there (there (there (there (there (here refl)))))


[6]⊆[0,1,2,3,4,5,6] : [ 6 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
[6]⊆[0,1,2,3,4,5,6] (here refl) = there (there (there (there (there (there (here refl))))))


[0]⊆[0,1,2,3,4,5,6,7] : [ 0 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ])
[0]⊆[0,1,2,3,4,5,6,7] (here refl) = here refl


[1]⊆[0,1,2,3,4,5,6,7] : [ 1 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ])
[1]⊆[0,1,2,3,4,5,6,7] (here refl) = there (here refl)


[2]⊆[0,1,2,3,4,5,6,7] : [ 2 ] ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ])
[2]⊆[0,1,2,3,4,5,6,7] (here refl) = there (there (here refl))


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


#[2]VAR2 : CTerm2
#[2]VAR2 = ct2 (VAR 2) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] VAR 2
    c = ⊆→⊆? [2]⊆[0,1,2]


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


#[1]LET : CTerm1 → CTerm2 → CTerm1
#[1]LET a b = ct1 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[2]LET : CTerm2 → CTerm3 → CTerm2
#[2]LET a b = ct2 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ [ 2 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                   (lowerVars-fvars-[0,1,2,3] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm3.closed b))))


#[3]LET : CTerm3 → CTerm4 → CTerm3
#[3]LET a b = ct3 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                   (lowerVars-fvars-[0,1,2,3,4] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm4.closed b))))


#[4]LET : CTerm4 → CTerm5 → CTerm4
#[4]LET a b = ct4 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed a))
                   (lowerVars-fvars-[0,1,2,3,4,5] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm5.closed b))))


#[5]LET : CTerm5 → CTerm6 → CTerm5
#[5]LET a b = ct5 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} (CTerm5.closed a))
                   (lowerVars-fvars-[0,1,2,3,4,5,6] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm6.closed b))))


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


#[4]VAR2 : CTerm4
#[4]VAR2 = ct4 (VAR 2) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] VAR 2
    c = ⊆→⊆? [2]⊆[0,1,2,3,4]


#[4]VAR3 : CTerm4
#[4]VAR3 = ct4 (VAR 3) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] VAR 3
    c = ⊆→⊆? [3]⊆[0,1,2,3,4]


#[4]VAR4 : CTerm4
#[4]VAR4 = ct4 (VAR 4) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] VAR 4
    c = ⊆→⊆? [4]⊆[0,1,2,3,4]


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


#[5]VAR2 : CTerm5
#[5]VAR2 = ct5 (VAR 2) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] VAR 2
    c = ⊆→⊆? [2]⊆[0,1,2,3,4,5]


#[5]VAR3 : CTerm5
#[5]VAR3 = ct5 (VAR 3) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] VAR 3
    c = ⊆→⊆? [3]⊆[0,1,2,3,4,5]


#[5]VAR4 : CTerm5
#[5]VAR4 = ct5 (VAR 4) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] VAR 4
    c = ⊆→⊆? [4]⊆[0,1,2,3,4,5]


#[5]VAR5 : CTerm5
#[5]VAR5 = ct5 (VAR 5) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] VAR 5
    c = ⊆→⊆? [5]⊆[0,1,2,3,4,5]


#[6]VAR0 : CTerm6
#[6]VAR0 = ct6 (VAR 0) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1,2,3,4,5,6]


#[6]VAR1 : CTerm6
#[6]VAR1 = ct6 (VAR 1) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1,2,3,4,5,6]


#[6]VAR2 : CTerm6
#[6]VAR2 = ct6 (VAR 2) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 2
    c = ⊆→⊆? [2]⊆[0,1,2,3,4,5,6]


#[6]VAR3 : CTerm6
#[6]VAR3 = ct6 (VAR 3) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 3
    c = ⊆→⊆? [3]⊆[0,1,2,3,4,5,6]


#[6]VAR4 : CTerm6
#[6]VAR4 = ct6 (VAR 4) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 4
    c = ⊆→⊆? [4]⊆[0,1,2,3,4,5,6]


#[6]VAR5 : CTerm6
#[6]VAR5 = ct6 (VAR 5) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 5
    c = ⊆→⊆? [5]⊆[0,1,2,3,4,5,6]


#[6]VAR6 : CTerm6
#[6]VAR6 = ct6 (VAR 6) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] VAR 6
    c = ⊆→⊆? [6]⊆[0,1,2,3,4,5,6]


#[7]VAR0 : CTerm7
#[7]VAR0 = ct7 (VAR 0) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1,2,3,4,5,6,7]


#[7]VAR1 : CTerm7
#[7]VAR1 = ct7 (VAR 1) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1,2,3,4,5,6,7]


#[7]VAR2 : CTerm7
#[7]VAR2 = ct7 (VAR 2) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] VAR 2
    c = ⊆→⊆? [2]⊆[0,1,2,3,4,5,6,7]


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


lowerVars2-fvars-[0,1,2,3,4,5,6] : {l : List Var}
                                   → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
                                   → lowerVars (lowerVars l) ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
lowerVars2-fvars-[0,1,2,3,4,5,6] {0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3,4,5,6] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3,4,5,6] {suc 0 ∷ l} h x = lowerVars2-fvars-[0,1,2,3,4,5,6] (λ z → h (there z)) x
lowerVars2-fvars-[0,1,2,3,4,5,6] {suc (suc z) ∷ l} h (here px) rewrite px = i w
  where
    w : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ])
    w = h (here refl)

    i : suc (suc z) ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]) →  z ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
    i (there (there (here q))) = here (suc-injective (suc-injective q)) --
    i (there (there (there (here q)))) = there (here (suc-injective (suc-injective q)))
    i (there (there (there (there (here q))))) = there (there (here (suc-injective (suc-injective q))))
    i (there (there (there (there (there (here q)))))) = there (there (there (here (suc-injective (suc-injective q)))))
    i (there (there (there (there (there (there (here q))))))) = there (there (there (there (here (suc-injective (suc-injective q))))))
lowerVars2-fvars-[0,1,2,3,4,5,6] {suc (suc z) ∷ l} h (there x) = lowerVars2-fvars-[0,1,2,3,4,5,6] (λ z → h (there z)) x


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


#[4]SPREAD : CTerm4 → CTerm6 → CTerm4
#[4]SPREAD a b = ct4 (SPREAD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] SPREAD ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (lowerVars (fvars ⌜ b ⌝))} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed a))
                   (lowerVars2-fvars-[0,1,2,3,4,5,6] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm6.closed b))))


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


#[4]FST : CTerm4 → CTerm4
#[4]FST t = #[4]SPREAD t #[6]VAR0


#[4]SND : CTerm4 → CTerm4
#[4]SND t = #[4]SPREAD t #[6]VAR1


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


#[2]LAMBDA : CTerm3 → CTerm2
#[2]LAMBDA b = ct2 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ [ 2 ]}
              (lowerVars-fvars-[0,1,2,3] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm3.closed b)))


#[3]LAMBDA : CTerm4 → CTerm3
#[3]LAMBDA b = ct3 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (lowerVars-fvars-[0,1,2,3,4] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm4.closed b)))


#[4]LAMBDA : CTerm5 → CTerm4
#[4]LAMBDA b = ct4 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
              (lowerVars-fvars-[0,1,2,3,4,5] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm5.closed b)))


#[5]LAMBDA : CTerm6 → CTerm5
#[5]LAMBDA b = ct5 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
              (lowerVars-fvars-[0,1,2,3,4,5,6] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm6.closed b)))


#[6]LAMBDA : CTerm7 → CTerm6
#[6]LAMBDA b = ct6 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]}
              (lowerVars-fvars-[0,1,2,3,4,5,6,7] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm7.closed b)))


#[3]IFLT : CTerm3 → CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]IFLT a b c d = ct3 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm3.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm3.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm3.closed c)) (⊆?→⊆ (CTerm3.closed d)))))


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


#[5]IFLT : CTerm5 → CTerm5 → CTerm5 → CTerm5 → CTerm5
#[5]IFLT a b c d = ct5 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm5.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm5.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm5.closed c)) (⊆?→⊆ (CTerm5.closed d)))))


#[6]IFLT : CTerm6 → CTerm6 → CTerm6 → CTerm6 → CTerm6
#[6]IFLT a b c d = ct6 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm6.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm6.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm6.closed c)) (⊆?→⊆ (CTerm6.closed d)))))


#[7]IFLT : CTerm7 → CTerm7 → CTerm7 → CTerm7 → CTerm7
#[7]IFLT a b c d = ct7 (IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] IFLT ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFLT0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm7.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm7.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                       (⊆?→⊆ (CTerm7.closed c)) (⊆?→⊆ (CTerm7.closed d)))))


#[3]IFEQ : CTerm3 → CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]IFEQ a b c d = ct3 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm3.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm3.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm3.closed c)) (⊆?→⊆ (CTerm3.closed d)))))


#[4]IFEQ : CTerm4 → CTerm4 → CTerm4 → CTerm4 → CTerm4
#[4]IFEQ a b c d = ct4 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm4.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm4.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm4.closed c)) (⊆?→⊆ (CTerm4.closed d)))))


#[5]IFEQ : CTerm5 → CTerm5 → CTerm5 → CTerm5 → CTerm5
#[5]IFEQ a b c d = ct5 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm5.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm5.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm5.closed c)) (⊆?→⊆ (CTerm5.closed d)))))


#[6]IFEQ : CTerm6 → CTerm6 → CTerm6 → CTerm6 → CTerm6
#[6]IFEQ a b c d = ct6 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm6.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm6.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                      (⊆?→⊆ (CTerm6.closed c)) (⊆?→⊆ (CTerm6.closed d)))))


#[7]IFEQ : CTerm7 → CTerm7 → CTerm7 → CTerm7 → CTerm7
#[7]IFEQ a b c d = ct7 (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
            (⊆?→⊆ (CTerm7.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝}
                 (⊆?→⊆ (CTerm7.closed b))
                 (⊆++ {Var} {fvars ⌜ c ⌝} {fvars ⌜ d ⌝}
                       (⊆?→⊆ (CTerm7.closed c)) (⊆?→⊆ (CTerm7.closed d)))))


#[4]APPLY : CTerm4 → CTerm4 → CTerm4
#[4]APPLY a b = ct4 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed b)))


#[5]APPLY : CTerm5 → CTerm5 → CTerm5
#[5]APPLY a b = ct5 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} (CTerm5.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} (CTerm5.closed b)))


#[6]APPLY : CTerm6 → CTerm6 → CTerm6
#[6]APPLY a b = ct6 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]} (CTerm6.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]} (CTerm6.closed b)))


#[7]APPLY : CTerm7 → CTerm7 → CTerm7
#[7]APPLY a b = ct7 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]} (CTerm7.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]} (CTerm7.closed b)))


CTerm3→4 : CTerm3 → CTerm4
CTerm3→4 t = ct4 ⌜ t ⌝ c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] ⌜ t ⌝
    c = ⊆→⊆? {fvars ⌜ t ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
              (⊆-trans (⊆?→⊆ (CTerm3.closed t)) [0,1,2,3]⊆[0,1,2,3,4])


#shiftUp0 : CTerm → CTerm
#shiftUp0 t = ct (shiftUp 0 ⌜ t ⌝) c
  where
    c : # (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0 ⌜ t ⌝ | CTerm.closed t = refl


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


#[5]shiftUp0 : CTerm4 → CTerm5
#[5]shiftUp0 t = ct5 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm4.cTerm t)) ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
            w = ⊆?→⊆ (CTerm4.closed t) {y} j

            z : y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
            z (here px) rewrite px = there (here refl)
            z (there (here px)) rewrite px = there (there (here refl))
            z (there (there (here px))) rewrite px = there (there (there (here refl)))
            z (there (there (there (here px)))) rewrite px = there (there (there (there (here refl))))
            z (there (there (there (there (here px))))) rewrite px = there (there (there (there (there (here refl)))))

            k : x ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
            k rewrite e | sym (suc≡sucIf≤0 y) = z w


#[6]shiftUp0 : CTerm5 → CTerm6
#[6]shiftUp0 t = ct6 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm5.cTerm t)) ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
            w = ⊆?→⊆ (CTerm5.closed t) {y} j

            z : y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]
            z (here px) rewrite px = there (here refl)
            z (there (here px)) rewrite px = there (there (here refl))
            z (there (there (here px))) rewrite px = there (there (there (here refl)))
            z (there (there (there (here px)))) rewrite px = there (there (there (there (here refl))))
            z (there (there (there (there (here px))))) rewrite px = there (there (there (there (there (here refl)))))
            z (there (there (there (there (there (here px)))))) rewrite px = there (there (there (there (there (there (here refl))))))

            k : x ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]
            k rewrite e | sym (suc≡sucIf≤0 y) = z w


#[7]shiftUp0 : CTerm6 → CTerm7
#[7]shiftUp0 t = ct7 (shiftUp 0 ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ] ] (shiftUp 0 ⌜ t ⌝)
    c rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ =
      ⊆→⊆? {Data.List.map (sucIf≤ 0) (fvars ⌜ t ⌝)} {0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]} s
      where
        s : Data.List.map (sucIf≤ 0) (fvars (CTerm6.cTerm t)) ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]
        s {x} i = k
          where
            y : Var
            y = fst (∈-map⁻ (sucIf≤ 0) i)

            j : y ∈ fvars ⌜ t ⌝
            j = fst (snd (∈-map⁻ (sucIf≤ 0) i))

            e : x ≡ sucIf≤ 0 y
            e = snd (snd (∈-map⁻ (sucIf≤ 0) i))

            w : y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ]
            w = ⊆?→⊆ (CTerm6.closed t) {y} j

            z : y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [ 6 ] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]
            z (here px) rewrite px = there (here refl)
            z (there (here px)) rewrite px = there (there (here refl))
            z (there (there (here px))) rewrite px = there (there (there (here refl)))
            z (there (there (there (here px)))) rewrite px = there (there (there (there (here refl))))
            z (there (there (there (there (here px))))) rewrite px = there (there (there (there (there (here refl)))))
            z (there (there (there (there (there (here px)))))) rewrite px = there (there (there (there (there (there (here refl))))))
            z (there (there (there (there (there (there (here px))))))) rewrite px = there (there (there (there (there (there (there (here refl)))))))

            k : x ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [ 7 ]
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


DECIDE⇛!₁ : {w : 𝕎·} {a a' b c : Term}
           → a ⇛! a' at w
           → DECIDE a b c ⇛! DECIDE a' b c at w
DECIDE⇛!₁ {w} {a} {a'} {b} {c} comp w1 e1 = lift (DECIDE⇓₁ z)
  where
    z : a ⇓ a' from w1 to w1
    z = lower (comp w1 e1)


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


⇓from-to→⊑ : {w w' : 𝕎·} {a b : Term}
               → a ⇓ b from w to w'
               → w ⊑· w'
⇓from-to→⊑ {w} {w'} {a} {b} (n , comp) = ≡ᵣ→⊑ (steps⊑ w n a) (→≡snd comp)


⇓NUM→SUC⇓NUM : {a : Term} {n : ℕ} {w1 w2 : 𝕎·}
                → a ⇓ NUM n from w1 to w2
                → SUC a ⇓ NUM (suc n) from w1 to w2
⇓NUM→SUC⇓NUM {a} {n} {w1} {w2} comp =
  ⇓-trans₂ {w1} {w2} {w2} {SUC a} {SUC (NUM n)} {NUM (suc n)} (SUC⇓ comp) (SUC-NUM⇓ w2 n)


SUC-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (SUC a , w) ≡ (SUC b , w'))
SUC-steps₁ {0} {w} {w'} {a} {b} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
SUC-steps₁ {suc k} {w} {w'} {a} {b} comp with is-NUM a
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w (suc k) tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (SUC a , w) ≡ (SUC b , w'))
    c with is-NUM a
    ... | inj₁ (x' , z) rewrite z = ⊥-elim (x x' refl)
    ... | inj₂ x' rewrite q = SUC-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


SUC⇓₁ : {w w' : 𝕎·} {a b : Term}
         → a ⇓ b from w to w'
         → SUC a ⇓ SUC b from w to w'
SUC⇓₁ {w} {w'} {a} {b} (k , comp) = SUC-steps₁ {k} {w} {w'} {a} {b} comp



SUC⇛₁ : {w : 𝕎·} {a a' : Term}
           → a ⇛ a' at w
           → SUC a ⇛ SUC a' at w
SUC⇛₁ {w} {a} {a'} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (SUC⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


SUC-NUM⇛ : (w : 𝕎·) (k : ℕ) → SUC (NUM k) ⇛ NUM (suc k) at w
SUC-NUM⇛ w k w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} (SUC-NUM⇓ w1 k))


SUC⇛₂ : {w : 𝕎·} {a : Term} {k : ℕ}
           → a ⇛ NUM k at w
           → SUC a ⇛ NUM (suc k) at w
SUC⇛₂ {w} {a} {k} comp = ⇛-trans (SUC⇛₁ comp) (SUC-NUM⇛ w k)


IFLT⇛₃ : {w : 𝕎·} {i j : ℕ} {a b u v : Term}
         → a ⇛ NUM i at w
         → b ⇛ NUM j at w
         → IFLT a b u v ⇛ IFLT (NUM i) (NUM j) u v at w
IFLT⇛₃ {w} {i} {j} {a} {b} {u} {v} c1 c2 w1 e1 =
  lift (⇓-from-to→⇓ {w1} {proj₁ c2'} (IFLT⇓₃ {w1} {fst c1'} {fst c2'} {i} {j} {a} {b} {u} {v} (snd c1') (snd c2')))
  where
    c1' : Σ 𝕎· (λ w' → a ⇓ NUM i from w1 to w')
    c1' = ⇓→from-to (lower (c1 w1 e1))

    c2' : Σ 𝕎· (λ w' → b ⇓ NUM j from (fst c1') to w')
    c2' = ⇓→from-to (lower (c2 (fst c1') (⊑-trans· e1 (⇓from-to→⊑ {w1} {fst c1'} {a} {NUM i} (snd c1')))))


IFEQ⇛₃ : {w : 𝕎·} {i j : ℕ} {a b u v : Term}
         → a ⇛ NUM i at w
         → b ⇛ NUM j at w
         → IFEQ a b u v ⇛ IFEQ (NUM i) (NUM j) u v at w
IFEQ⇛₃ {w} {i} {j} {a} {b} {u} {v} c1 c2 w1 e1 =
  lift (⇓-from-to→⇓ {w1} {proj₁ c2'} (IFEQ⇓₃ {w1} {fst c1'} {fst c2'} {i} {j} {a} {b} {u} {v} (snd c1') (snd c2')))
  where
    c1' : Σ 𝕎· (λ w' → a ⇓ NUM i from w1 to w')
    c1' = ⇓→from-to (lower (c1 w1 e1))

    c2' : Σ 𝕎· (λ w' → b ⇓ NUM j from (fst c1') to w')
    c2' = ⇓→from-to (lower (c2 (fst c1') (⊑-trans· e1 (⇓from-to→⊑ {w1} {fst c1'} {a} {NUM i} (snd c1')))))


INL¬≡INR : {a b : Term} → ¬ (INL a) ≡ INR b
INL¬≡INR {a} {b} ()


#INL¬≡INR : {a b : CTerm} → ¬ (#INL a) ≡ #INR b
#INL¬≡INR {a} {b} x = INL¬≡INR {⌜ a ⌝} {⌜ b ⌝} (≡CTerm x)


#⇓#INL→¬#⇛!#INR : (w : 𝕎·) (t a b c f g : CTerm)
                    → t #⇓ #SUP a f at w
                    → t #⇓ #SUP (#INL b) g at w
                    → a #⇛! #INR c at w
                    → ⊥
#⇓#INL→¬#⇛!#INR w t a b c f g c1 c2 c3
  rewrite #SUPinj1 {a} {f} {#INL b} {g} (#⇓-val-det {w} {t} {#SUP a f} {#SUP (#INL b) g} tt tt c1 c2)
  = #INL¬≡INR (#⇛!→≡ {#INL b} {#INR c} {w} c3 tt)


#INL→¬#⇛!#INR : (w : 𝕎·) (a b c : CTerm)
                   → a ≡ #INL b
                   → a #⇛! #INR c at w
                   → ⊥
#INL→¬#⇛!#INR w a b c e comp
  rewrite e
  = #INL¬≡INR (#⇛!→≡ {#INL b} {#INR c} {w} comp tt)


APPLY-FIX⇓→ : (w : 𝕎·) (F a v : Term)
               → isValue v
               → APPLY (FIX (LAMBDA F)) a ⇓ v at w
               → APPLY (sub (FIX (LAMBDA F)) F) a ⇓ v at w
APPLY-FIX⇓→ w F a v isv (0 , comp) rewrite sym comp = ⊥-elim isv
APPLY-FIX⇓→ w F a v isv (suc n , comp) = n , comp


APPLY2-FIX⇓→ : (w : 𝕎·) (F a b v : Term)
                → isValue v
                → APPLY2 (FIX (LAMBDA F)) a b ⇓ v at w
                → APPLY2 (sub (FIX (LAMBDA F)) F) a b ⇓ v at w
APPLY2-FIX⇓→ w F a b v isv (0 , comp) rewrite sym comp = ⊥-elim isv
APPLY2-FIX⇓→ w F a b v isv (suc n , comp) = n , comp


APPLY-LAMBDA⇓val→ : {w : 𝕎·} {f a v : Term}
                     → isValue v
                     → APPLY (LAMBDA f) a ⇓ v at w
                     → sub a f ⇓ v at w
APPLY-LAMBDA⇓val→ {w} {f} {a} {v} isv (0 , comp) rewrite sym comp = ⊥-elim isv
APPLY-LAMBDA⇓val→ {w} {f} {a} {v} isv (suc n , comp) = n , comp


APPLY2-LAMBDA⇓val→ : {w : 𝕎·} {f a b v : Term}
                      → isValue v
                      → APPLY2 (LAMBDA (LAMBDA f)) a b ⇓ v at w
                      → APPLY (sub a (LAMBDA f)) b ⇓ v at w
APPLY2-LAMBDA⇓val→ {w} {f} {a} {b} {v} isv (0 , comp) rewrite sym comp = ⊥-elim isv
APPLY2-LAMBDA⇓val→ {w} {f} {a} {b} {v} isv (suc n , comp) = n , comp


LET-steps-val→ : {n : ℕ} {w1 w2 : 𝕎·} {a b v : Term}
                  → isValue v
                  → steps n (LET a b , w1) ≡ (v , w2)
                  → Σ Term (λ u → Σ 𝕎· (λ w → isValue u × a ⇓ u from w1 to w × sub u b ⇓ v from w to w2))
LET-steps-val→ {0} {w1} {w2} {a} {b} {v} isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
LET-steps-val→ {suc n} {w1} {w2} {a} {b} {v} isv comp with isValue⊎ a
... | inj₁ x = a , w1 , x , (0 , refl) , (n , comp)
... | inj₂ x with step⊎ a w1
... |    inj₁ (y , w' , q) rewrite q =
  fst ind , fst (snd ind) , fst (snd (snd ind)) ,
  step-⇓-from-to-trans {w1} {w'} {proj₁ (snd ind)} {a} {y} {proj₁ ind} q (fst (snd (snd (snd ind)))) ,
  snd (snd (snd (snd ind)))
  where
    ind : Σ Term (λ u → Σ 𝕎· (λ w → isValue u × y ⇓ u from w' to w × sub u b ⇓ v from w to w2))
    ind = LET-steps-val→ {n} {w'} {w2} {y} {b} {v} isv comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


LET⇓val→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → LET a b ⇓ v at w
            → Σ Term (λ u → Σ 𝕎· (λ w' → isValue u × a ⇓ u from w to w' × sub u b ⇓ v at w'))
LET⇓val→ {w} {a} {b} {v} isv comp =
  fst j2 , fst (snd j2) , fst (snd (snd j2)) , fst (snd (snd (snd j2))) ,
  ⇓-from-to→⇓ {proj₁ (snd j2)} {proj₁ j1} {sub (proj₁ j2) b} {v} (snd (snd (snd (snd j2))))
  where
    j1 : Σ 𝕎· (λ w' → LET a b ⇓ v from w to w')
    j1 = ⇓→from-to {w} {LET a b} {v} comp

    j2 : Σ Term (λ u → Σ 𝕎· (λ w' → isValue u × a ⇓ u from w to w' × sub u b ⇓ v from w' to fst j1))
    j2 = LET-steps-val→ {proj₁ (snd j1)} {w} {proj₁ j1} {a} {b} {v} isv (snd (snd j1))


LET-val⇓val→ : {w : 𝕎·} {a b v u : Term}
            → isValue v
            → isValue u
            → a ⇓ u at w
            → LET a b ⇓ v at w
            → Σ 𝕎· (λ w' → a ⇓ u from w to w' × sub u b ⇓ v at w')
LET-val⇓val→ {w} {a} {b} {v} {u} isv isu compa comp =
  w1 , comp1' , comp2'
  where
    j1 : Σ Term (λ u → Σ 𝕎· (λ w' → isValue u × a ⇓ u from w to w' × sub u b ⇓ v at w'))
    j1 = LET⇓val→ {w} {a} {b} {v} isv comp

    u1 : Term
    u1 = fst j1

    w1 : 𝕎·
    w1 = fst (snd j1)

    isu1 : isValue u1
    isu1 = fst (snd (snd j1))

    comp1 : a ⇓ u1 from w to w1
    comp1 = fst (snd (snd (snd j1)))

    comp2 : sub u1 b ⇓ v at w1
    comp2 = snd (snd (snd (snd j1)))

    comp1' : a ⇓ u from w to w1
    comp1' rewrite ⇓-val-det {w} {a} {u} {u1} isu isu1 compa (⇓-from-to→⇓ {w} {w1} {a} {u1} comp1) = comp1

    comp2' : sub u b ⇓ v at w1
    comp2' rewrite ⇓-val-det {w} {a} {u} {u1} isu isu1 compa (⇓-from-to→⇓ {w} {w1} {a} {u1} comp1) = comp2


≡ₗ→⇓ : {a b c : Term} {w : 𝕎·} → a ≡ b → a ⇓ c at w → b ⇓ c at w
≡ₗ→⇓ {a} {b} {c} {w} e comp rewrite e = comp



→≡#APPLY : {a b c d : CTerm} → a ≡ c → b ≡ d → #APPLY a b ≡ #APPLY c d
→≡#APPLY {a} {b} {c} {d} e f rewrite e | f = refl



APPLY-MSEQ⇓ : (w : 𝕎·) (s : 𝕊) (a : Term) (k : ℕ)
             → a ⇓ NUM k at w
             → APPLY (MSEQ s) a ⇓ NUM (s k) at w
APPLY-MSEQ⇓ w s a k comp =
  step-⇓-trans {w} {w} refl
    (⇓-from-to→⇓
      {w} {proj₁ comp1}
      (⇓-trans₂ {w} {proj₁ comp1} {proj₁ comp1} {MAPP s a} {MAPP s (NUM k)} (MAPP⇓ s (snd comp1)) (1 , refl)))
  where
    comp1 : Σ 𝕎· (λ w' → a ⇓ NUM k from w to w')
    comp1 = ⇓→from-to {w} {a} {NUM k} comp


APPLY-MSEQ⇛ : (w : 𝕎·) (s : 𝕊) (a : Term) (k : ℕ)
             → a ⇛ NUM k at w
             → APPLY (MSEQ s) a ⇛ NUM (s k) at w
APPLY-MSEQ⇛ w s a k comp w1 e1 = lift (APPLY-MSEQ⇓ w1 s a k (lower (comp w1 e1)))


#FST-shiftUp : (a : CTerm) → # FST (shiftUp 0 ⌜ a ⌝)
#FST-shiftUp a rewrite →#shiftUp 0 {⌜ a ⌝} (CTerm.closed a) = refl


#SND-shiftUp : (a : CTerm) → # SND (shiftUp 0 ⌜ a ⌝)
#SND-shiftUp a rewrite →#shiftUp 0 {⌜ a ⌝} (CTerm.closed a) = refl


#APPLY2 : CTerm → CTerm → CTerm → CTerm
#APPLY2 a b c = #APPLY (#APPLY a b) c


#[0]APPLY2 : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]APPLY2 a b c = #[0]APPLY (#[0]APPLY a b) c


#[1]APPLY2 : CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]APPLY2 a b c = #[1]APPLY (#[1]APPLY a b) c


#[2]APPLY2 : CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]APPLY2 a b c = #[2]APPLY (#[2]APPLY a b) c


#[3]APPLY2 : CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]APPLY2 a b c = #[3]APPLY (#[3]APPLY a b) c


#[4]APPLY2 : CTerm3 → CTerm3 → CTerm3 → CTerm3
#[4]APPLY2 a b c = #[3]APPLY (#[3]APPLY a b) c


#[5]APPLY2 : CTerm5 → CTerm5 → CTerm5 → CTerm5
#[5]APPLY2 a b c = #[5]APPLY (#[5]APPLY a b) c


#[6]APPLY2 : CTerm6 → CTerm6 → CTerm6 → CTerm6
#[6]APPLY2 a b c = #[6]APPLY (#[6]APPLY a b) c


ID : Term
ID = LAMBDA (VAR 0)


BOT : Term
BOT = FIX ID


#ID : CTerm
#ID = #LAMBDA #[0]VAR


#BOT : CTerm
#BOT = #FIX #ID


#[0]FIX : CTerm0 → CTerm0
#[0]FIX a = ct0 (FIX ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] FIX ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {[ 0 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))


#[0]ID : CTerm0
#[0]ID = #[0]LAMBDA #[1]VAR0


#[0]BOT : CTerm0
#[0]BOT = #[0]FIX #[0]ID


#[0]N0 : CTerm0
#[0]N0 = #[0]NUM 0


#[1]FIX : CTerm1 → CTerm1
#[1]FIX a = ct1 (FIX ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] FIX ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ [ 1 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))


#[1]ID : CTerm1
#[1]ID = #[1]LAMBDA #[2]VAR0


#[1]BOT : CTerm1
#[1]BOT = #[1]FIX #[1]ID


#[1]N0 : CTerm1
#[1]N0 = #[1]NUM 0


#[2]FIX : CTerm2 → CTerm2
#[2]FIX a = ct2 (FIX ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] FIX ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ [ 2 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))


#[2]ID : CTerm2
#[2]ID = #[2]LAMBDA #[3]VAR0


#[2]BOT : CTerm2
#[2]BOT = #[2]FIX #[2]ID


#[2]N0 : CTerm2
#[2]N0 = #[2]NUM 0


#[3]FIX : CTerm3 → CTerm3
#[3]FIX a = ct3 (FIX ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] FIX ⌜ a ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))


#[3]ID : CTerm3
#[3]ID = #[3]LAMBDA #[4]VAR0


#[3]BOT : CTerm3
#[3]BOT = #[3]FIX #[3]ID


#[3]N0 : CTerm3
#[3]N0 = #[3]NUM 0

\end{code}
