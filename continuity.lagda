\begin{code}
{-# OPTIONS --rewriting #-}
--{-# OPTIONS --auto-inline #-}

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
open import Axiom.Extensionality.Propositional


open import util
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
open import choiceBar


module continuity {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                  (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                  (X : ChoiceExt W C)
                  (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                  (F : Freeze {L} W C K P G N)
                  (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                  (CB : ChoiceBar W M C K P G X N V F E) -- TODO - We won't need everything from there: use a different module
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)

{--
open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)
--}

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)



-- turns 'f' into λy.(if n ≤ y then name:=ℂ₁);f(y)
-- ℂ₀ is treated as true here (i.e., "didn't reach n"), and ℂ₁ as false (i.e., "reached at least n")
bound : (name : Name) (n : Term) (f : Term) → Term
bound name n f = LAMBDA (SEQ (IFLE n (VAR 0) (CHOOSE (NAME name) (ℂ→T ℂ₁·)) AX) (APPLY f (VAR 0)))


-- TODO: the name should be a fresh name, that does not occur in F
-- TODO: need union types?


set : (name : Name) → Term
set name = CHOOSE (NAME name) (ℂ→T ℂ₀·)


-- Assuming that choices are numbers
--IFC0 : Term → Term → Term → Term
--IFC0 a b c = IFLT (get0 name) (NUM 1)



probe : (name : Name) (F : Term) (n : Term) (f : Term) → Term
probe name F n f = LET (APPLY F (bound name n f))
                       (IFLT (get0 name) (NUM 1) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains 0 (i.e., < 1 -- we assume here that choices are numbers)


oldtest : (name : Name) (F : Term) (n : Term) (f : Term) → Term
oldtest name F n f = LET (APPLY F (bound name n f))
                         (LET (IFLT (get0 name) (NUM 1) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains ℂ₀
                              (SEQ (set name) -- resets the reference to ℂ₀
                                   (VAR 0)))


test : (name : Name) (F : Term) (n : Term) (f : Term) → Term
test name F n f = SEQ (set name) (probe name F n f)


set0 : (name : Name) → Term
set0 name = setT name (NUM 0)


appUpd : (name : Name) (F f : Term) → Term
appUpd name F f = APPLY F (upd name f)


probeM : (name : Name) (F f : Term) → Term
probeM name F f = SEQ (appUpd name F f) (get0 name)


testM : (name : Name) (F f : Term) → Term
testM name F f = SEQ (set0 name) (probeM name F f)


νtestM : (F f : Term) → Term
νtestM F f = FRESH (testM 0 F f)


NATn : Term → Term
NATn n = SET NAT (LT (VAR 0) (shiftUp 0 n))


BAIREn : Term → Term
BAIREn n = FUN (NATn n) NAT


-- TODO:
-- We need to truncate this type using SUBSING
-- Then, prove that testM is a NAT
-- We will need:
--  + to assume that the choice is over nats
--  + that it's actually a time invariant nat, which requires
--    * F and f to not read choices, but they can write
contBody : (F f : Term) → Term
contBody F f = SUM NAT (PI BAIRE (FUN (EQ f (VAR 0) (BAIREn (VAR 1))) (EQ (APPLY F f) (APPLY F (VAR 0)) NAT)))




-- MOVE to terms
#BAIRE : CTerm
#BAIRE = ct BAIRE c
  where
    c : # BAIRE
    c = refl


-- MOVE to terms
BAIRE→NAT : Term
BAIRE→NAT = FUN BAIRE NAT


-- MOVE to terms
#BAIRE→NAT : CTerm
#BAIRE→NAT = ct BAIRE→NAT c
  where
    c : # BAIRE→NAT
    c = refl


-- MOVE to terms
#BAIRE→NAT≡ : #BAIRE→NAT ≡ #FUN #BAIRE #NAT
#BAIRE→NAT≡ = refl


-- MOVE to terms
BAIRE→NAT! : Term
BAIRE→NAT! = FUN BAIRE NAT!


-- MOVE to terms
#BAIRE→NAT! : CTerm
#BAIRE→NAT! = ct BAIRE→NAT! c
  where
    c : # BAIRE→NAT!
    c = refl


-- MOVE to terms
#BAIRE→NAT!≡ : #BAIRE→NAT! ≡ #FUN #BAIRE #NAT!
#BAIRE→NAT!≡ = refl


-- MOVE to terms
#BAIRE≡ : #BAIRE ≡ #FUN #NAT #NAT
#BAIRE≡ = refl


-- MOVE to terms
#LAMBDA : CTerm0 → CTerm
#LAMBDA a = ct (LAMBDA ⌜ a ⌝) c
  where
    c : # LAMBDA (CTerm0.cTerm a)
    c rewrite lowerVars-fvars-CTerm0≡[] a = refl


-- MOVE to terms
fvars-SEQ0 : (a b : Term) → fvars (SEQ a b) ≡ fvars a ++ fvars b
fvars-SEQ0 a b rewrite fvars-shiftUp≡ 0 b | lowerVars-map-sucIf≤-suc 0 (fvars b) | loweVars-suc (fvars b) = refl


-- MOVE to terms
#SEQ : CTerm → CTerm → CTerm
#SEQ a b = ct (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ | CTerm.closed a | CTerm.closed b = refl


-- MOVE to terms
#[0]SEQ : CTerm0 → CTerm0 → CTerm0
#[0]SEQ a b = ct0 (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                           (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))



-- MOVE to terms
fvars-ITE : (a b c : Term) → fvars (ITE a b c) ≡ fvars a ++ fvars b ++ fvars c
fvars-ITE a b c
  rewrite fvars-shiftUp≡ 0 b
        | lowerVars-map-sucIf≤-suc 0 (fvars b)
        | loweVars-suc (fvars b)
        | fvars-shiftUp≡ 0 c
        | lowerVars-map-sucIf≤-suc 0 (fvars c)
        | loweVars-suc (fvars c) = refl


-- MOVE to terms
fvars-IF-THEN : (a b : Term) → fvars (IF-THEN a b) ≡ fvars a ++ fvars b
fvars-IF-THEN a b rewrite fvars-ITE a b AX | ++[] (fvars b) = refl


-- MOVE to terms
fvars-IFLE : (a b c d : Term) → fvars (IFLE a b c d) ≡ fvars b ++ fvars a ++ fvars d ++ fvars c
fvars-IFLE a b c d = refl


-- MOVE to terms
#[0]IF-THEN : CTerm0 → CTerm0 → CTerm0
#[0]IF-THEN a b = ct0 (IF-THEN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] IF-THEN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-IF-THEN ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))


-- MOVE to terms
#IF-THEN : CTerm → CTerm → CTerm
#IF-THEN a b = ct (IF-THEN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # IF-THEN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-IF-THEN ⌜ a ⌝ ⌜ b ⌝ | CTerm.closed a | CTerm.closed b = refl



-- MOVE to terms
#[0]IFLE : CTerm0 → CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]IFLE a b c d = ct0 (IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) cl
  where
    cl : #[ [ 0 ] ] IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    cl rewrite fvars-IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ b ⌝ ++ fvars ⌜ a ⌝ ++ fvars ⌜ d ⌝ ++ fvars ⌜ c ⌝}
            {[ 0 ]}
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ a ⌝ ++ fvars ⌜ d ⌝ ++ fvars ⌜ c ⌝}
                 (⊆?→⊆ (CTerm0.closed b))
                 (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ d ⌝ ++ fvars ⌜ c ⌝}
                      (⊆?→⊆ (CTerm0.closed a))
                      (⊆++ {Var} {fvars ⌜ d ⌝} {fvars ⌜ c ⌝}
                           (⊆?→⊆ (CTerm0.closed d))
                           (⊆?→⊆ (CTerm0.closed c)))))


-- MOVE to terms
#IFLE : CTerm → CTerm → CTerm → CTerm → CTerm
#IFLE a b c d = ct (IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) cl
  where
    cl : # IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    cl rewrite fvars-IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ | CTerm.closed a | CTerm.closed b | CTerm.closed c | CTerm.closed d = refl


-- MOVE to terms
#[0]LE : CTerm0 → CTerm0 → CTerm0
#[0]LE a b = ct0 (LE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LE ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-NEG (LT ⌜ b ⌝ ⌜ a ⌝) = ⊆→⊆? {fvars ⌜ b ⌝ ++ fvars ⌜ a ⌝ } {[ 0 ]}
                                               (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b))
                                                    (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a)))


-- MOVE to terms
#LE : CTerm → CTerm → CTerm
#LE a b = ct (LE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # LE ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-NEG (LT ⌜ b ⌝ ⌜ a ⌝) | CTerm.closed a | CTerm.closed b = refl


-- MOVE to terms
#[0]CHOOSE : CTerm0 → CTerm0 → CTerm0
#[0]CHOOSE a b = ct0 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


-- MOVE to terms
#CHOOSE : CTerm → CTerm → CTerm
#CHOOSE a b = ct (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl



#bound : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#bound name n f = ct (bound name ⌜ n ⌝ ⌜ f ⌝) c
  where
    c : # bound name ⌜ n ⌝ ⌜ f ⌝
    c rewrite CTerm.closed n | CTerm.closed f
            | #shiftUp 0 (ℂ→C· ℂ₁·)
            | lowerVars-fvars-CTerm≡[] (ℂ→C· ℂ₁·)
            | lowerVarsApp (fvars (shiftUp 0 ⌜ f ⌝)) [ 1 ]
            | #shiftUp 0 f
            | lowerVars-fvars-CTerm≡[] f
            | lowerVarsApp (fvars ⌜ ℂ→C· ℂ₁· ⌝) [ 0 ]
            | lowerVars-fvars-CTerm≡[] (ℂ→C· ℂ₁·) = refl



#upd : (name : Name) (f : CTerm) → CTerm
#upd name f = ct (upd name ⌜ f ⌝) c
  where
    c : # upd name ⌜ f ⌝
    c rewrite CTerm.closed f
            | #shiftUp 0 f
            | lowerVarsApp (fvars ⌜ f ⌝) [ 1 ]
            | lowerVars-fvars-CTerm≡[] f = refl


#set : (name : Name) → CTerm
#set name = ct (set name) c
  where
    c : # set name
    c rewrite CTerm.closed (ℂ→C· ℂ₀·) = refl


#set0 : (name : Name) → CTerm
#set0 name = ct (set0 name) c
  where
    c : # set0 name
    c = refl

#get0 : (name : Name) → CTerm
#get0 name = ct (get0 name) c
  where
    c : # get0 name
    c = refl



#probe : (name : Name) (F n f : CTerm) → CTerm
#probe name F n f = ct (probe name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝) c
  where
    c : # probe name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝
    c rewrite CTerm.closed (#bound name n f)
            | CTerm.closed F = refl


#probeM : (name : Name) (F f : CTerm) → CTerm
#probeM name F f = ct (probeM name ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # probeM name ⌜ F ⌝ ⌜ f ⌝
    c rewrite CTerm.closed (#upd name f)
            | CTerm.closed F = refl


#test : (name : Name) (F : CTerm) (n : CTerm) (f : CTerm) → CTerm
#test name F n f = ct (test name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝) c
  where
    c : # test name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝
    c rewrite fvars-SEQ0 (set name) (probe name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝)
            | CTerm.closed (#set name)
            | CTerm.closed (#bound name n f)
            | lowerVarsApp (fvars ⌜ ℂ→C· ℂ₀· ⌝) [ 0 ]
            | lowerVars-fvars-CTerm≡[] (ℂ→C· ℂ₀·)
            | CTerm.closed F = refl



#testM : (name : Name) (F f : CTerm) → CTerm
#testM name F f = ct (testM name ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # testM name ⌜ F ⌝ ⌜ f ⌝
    c rewrite fvars-SEQ0 (set0 name) (probeM name ⌜ F ⌝ ⌜ f ⌝)
            | CTerm.closed (#set0 name)
            | CTerm.closed (#get0 name)
            | CTerm.closed (#upd name f)
            | CTerm.closed F = refl



#νtestM : (F f : CTerm) → CTerm
#νtestM F f = ct (νtestM ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # νtestM ⌜ F ⌝ ⌜ f ⌝
    c = CTerm.closed (#testM 0 F f)



#[0]AX : CTerm0
#[0]AX = ct0 AX refl


#BOUND : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#BOUND name n f =
  #LAMBDA (#[0]SEQ (#[0]IFLE ⌞ n ⌟ #[0]VAR (#[0]CHOOSE (#[0]NAME name) ⌞ ℂ→C· ℂ₁· ⌟) #[0]AX)
                   (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#bound≡ : (name : Name) (n : CTerm) (f : CTerm) → #bound name n f ≡ #BOUND name n f
#bound≡ name n f = CTerm≡ refl



-- MOVE to terms
#[0]LET : CTerm0 → CTerm1 → CTerm0
#[0]LET a b = ct0 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))



-- MOVE to terms
#[1]SEQ : CTerm1 → CTerm1 → CTerm1
#[1]SEQ a b = ct1 (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


-- MOVE to terms
#[1]CHOOSE : CTerm1 → CTerm1 → CTerm1
#[1]CHOOSE a b = ct1 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


-- MOVE to terms
#[1]CS : Name → CTerm1
#[1]CS name = ct1 (CS name) c
  where
    c : #[ 0 ∷ [ 1 ] ] CS name
    c = refl


-- MOVE to terms
#[1]NAME : Name → CTerm1
#[1]NAME name = ct1 (NAME name) c
  where
    c : #[ 0 ∷ [ 1 ] ] NAME name
    c = refl



#updGt : (name : Name) (t : CTerm) → CTerm
#updGt name t = ct (updGt name ⌜ t ⌝) c
  where
    c : # updGt  name ⌜ t ⌝
    c rewrite CTerm.closed (#get0 name) | CTerm.closed t = refl


#[0]updGt : (name : Name) (t : CTerm0) → CTerm0
#[0]updGt name t = ct0 (updGt name ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] updGt  name ⌜ t ⌝
    c rewrite CTerm.closed (#get0 name) | ++[] (fvars ⌜ t ⌝) =
      ⊆→⊆? {fvars ⌜ t ⌝ ++ fvars ⌜ t ⌝} {[ 0 ]} (⊆++ (⊆?→⊆ {fvars ⌜ t ⌝} {[ 0 ]} (CTerm0.closed t))
                                                    (⊆?→⊆ {fvars ⌜ t ⌝} {[ 0 ]} (CTerm0.closed t)))


#[1]updGt : (name : Name) (t : CTerm1) → CTerm1
#[1]updGt name t = ct1 (updGt name ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] updGt  name ⌜ t ⌝
    c rewrite CTerm.closed (#get0 name) | ++[] (fvars ⌜ t ⌝) =
      ⊆→⊆? {fvars ⌜ t ⌝ ++ fvars ⌜ t ⌝} {0 ∷ [ 1 ]} (⊆++ (⊆?→⊆ {fvars ⌜ t ⌝} {0 ∷ [ 1 ]} (CTerm1.closed t))
                                                        (⊆?→⊆ {fvars ⌜ t ⌝} {0 ∷ [ 1 ]} (CTerm1.closed t)))


#UPD : (name : Name) (f : CTerm) → CTerm
#UPD name f = #LAMBDA (#[0]LET #[0]VAR (#[1]SEQ (#[1]updGt name #[1]VAR0) (#[1]APPLY ⌞ f ⌟ #[1]VAR0)))


#upd≡ : (name : Name) (f : CTerm) → #upd name f ≡ #UPD name f
#upd≡ name f = CTerm≡ refl


-- MOVE to terms
#LET : CTerm → CTerm0 → CTerm
#LET a b = ct (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # LET ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b = refl


#probeM≡ : (name : Name) (F f : CTerm) → #probeM name F f ≡ #SEQ (#APPLY F (#upd name f)) (#get0 name)
#probeM≡ name F f = CTerm≡ refl


#testM≡ : (name : Name) (F f : CTerm) → #testM name F f ≡ #SEQ (#set0 name) (#probeM name F f)
#testM≡ name F f = CTerm≡ refl


--→≡APPLY : {a₁ a₂ b₁ b₂ : Term} → a₁ ≡ a₂ → b₁ ≡ b₂ → APPLY a₁ b₁ ≡ APPLY a₂ b₂
--→≡APPLY e f rewrite e | f = refl


sub-SEQ : (a b c : Term) → # a → #[ [ 0 ] ] c → sub a (SEQ b c) ≡ SEQ (sub a b) (sub a c)
sub-SEQ a b c ca cc
  rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | #shiftDown 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftUp 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
  = →≡LET refl refl


→sub-SEQ : {a b c b' c' : Term} → # a → #[ [ 0 ] ] c
            → sub a b ≡ b'
            → sub a c ≡ c'
            → sub a (SEQ b c) ≡ SEQ b' c'
→sub-SEQ {a} {b} {c} {b'} {c'} ca cc eb ec rewrite sym eb | sym ec = sub-SEQ a b c ca cc


sub-ITE : (a b c d : Term) → # a → #[ [ 0 ] ] c → #[ [ 0 ] ] d
          → sub a (ITE b c d) ≡ ITE (sub a b) (sub a c) (sub a d)
sub-ITE a b c d ca cc cd
  rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | shiftDown1-subv1-shiftUp0 0 a d ca
        | #shiftDown 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftUp 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftDown 0 (ct (subv 0 a d) (#subv-CTerm (ct a ca) (ct0 d cd)))
        | #shiftUp 0 (ct (subv 0 a d) (#subv-CTerm (ct a ca) (ct0 d cd)))
  = refl


sub-IF-THEN : (a b c : Term) → # a → #[ [ 0 ] ] c
              → sub a (IF-THEN b c) ≡ IF-THEN (sub a b) (sub a c)
sub-IF-THEN a b c ca cc = sub-ITE a b c AX ca cc refl


→sub-IF-THEN : {a b c b' c' : Term} → # a → #[ [ 0 ] ] c
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a (IF-THEN b c) ≡ IF-THEN b' c'
→sub-IF-THEN {a} {b} {c} {b'} {c'} ca cc eb ec rewrite sym eb | sym ec = sub-IF-THEN a b c ca cc




sub-IFLE : (a b c d e : Term)
           → sub a (IFLE b c d e) ≡ IFLE (sub a b) (sub a c) (sub a d) (sub a e)
sub-IFLE a b c d e = refl


→sub-IFLE : {a b c d e b' c' d' e' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a e ≡ e'
                → sub a (IFLE b c d e) ≡ IFLE b' c' d' e'
→sub-IFLE {a} {b} {c} {d} {e} {b'} {c'} {d'} {e'} eb ec ed ee
  rewrite sym eb | sym ec | sym ed | sym ee =
  refl


sub-LE : (a b c : Term) → sub a (LE b c) ≡ LE (sub a b) (sub a c)
sub-LE a b c = refl


→sub-LE : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (LE b c) ≡ LE b' c'
→sub-LE {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-LE a b c


→sub-APPLY : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (APPLY b c) ≡ APPLY b' c'
→sub-APPLY {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-APPLY a b c


{--
sub-IFC0 : (a b c d : Term)
           → sub a (IFC0 b c d) ≡ IFC0 (sub a b) (sub a c) (sub a d)
sub-IFC0 a b c d = refl
--}


{--
→sub-IFC0 : {a b c d b' c' d' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a (IFC0 b c d) ≡ IFC0 b' c' d'
→sub-IFC0 {a} {b} {c} {d} {b'} {c'} {d'} eb ec ed
  rewrite sym eb | sym ec | sym ed =
  refl
--}


#⇛!-#APPLY-#BOUND : (w : 𝕎·) (name : Name) (n : CTerm) (f : CTerm) (a : CTerm)
                     → #APPLY (#BOUND name n f) a #⇛! #SEQ (#IFLE n a (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a) at w
#⇛!-#APPLY-#BOUND w name n f a w1 e1
  = lift (1 , →≡pair (→sub-SEQ {⌜ a ⌝}
                                 {⌜ #[0]IFLE ⌞ n ⌟ #[0]VAR (#[0]CHOOSE (#[0]NAME name) ⌞ ℂ→C· ℂ₁· ⌟) #[0]AX ⌝}
                                 {⌜ #[0]APPLY ⌞ f ⌟ #[0]VAR ⌝}
                                 {⌜ #IFLE n a (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·)) #AX ⌝}
                                 {⌜ #APPLY f a ⌝}
                                 (CTerm.closed a) (CTerm0.closed (#[0]APPLY ⌞ f ⌟ #[0]VAR))
                                 (→sub-IFLE {⌜ a ⌝} {⌜ n ⌝} {⌜ #[0]VAR ⌝} {⌜ #[0]CHOOSE (#[0]NAME name) ⌞ ℂ→C· ℂ₁· ⌟ ⌝} {⌜ #AX ⌝}
                                             (subNotIn ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n))
                                             (sub-VAR0 ⌜ a ⌝)
                                             (subNotIn ⌜ a ⌝ ⌜ #CHOOSE (#NAME name) (ℂ→C· ℂ₁·) ⌝ (CTerm.closed (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·))))
                                             (subNotIn ⌜ a ⌝ ⌜ #AX ⌝ refl))
                                 (→sub-APPLY {⌜ a ⌝} {⌜ f ⌝} {⌜ #[0]VAR ⌝} (subNotIn ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)) (sub-VAR0 ⌜ a ⌝))) refl)


-- MOVE to props2/3
eqTypesBAIRE : {w : 𝕎·} {i : ℕ} → isType i w #BAIRE
eqTypesBAIRE {w} {i} = ≡CTerm→eqTypes (sym #BAIRE≡) (sym #BAIRE≡) (eqTypesFUN← eqTypesNAT eqTypesNAT)



-- MOVE to props2/3
≡CTerm→equalInTypeₗ : {u : ℕ} {w : 𝕎·} {A a a' b : CTerm}
                      → a ≡ a'
                      → equalInType u w A a b
                      → equalInType u w A a' b
≡CTerm→equalInTypeₗ {u} {w} {A} {a} {a'} {b} e z rewrite e = z


-- MOVE to props2/3
≡CTerm→equalInTypeᵣ : {u : ℕ} {w : 𝕎·} {A a b b' : CTerm}
                      → b ≡ b'
                      → equalInType u w A a b
                      → equalInType u w A a b'
≡CTerm→equalInTypeᵣ {u} {w} {A} {a} {b} {b'} e z rewrite e = z


-- MOVE to props2/3
≡CTerm→∈Type : {u : ℕ} {w : 𝕎·} {A a a' : CTerm}
                      → a ≡ a'
                      → ∈Type u w A a
                      → ∈Type u w A a'
≡CTerm→∈Type {u} {w} {A} {a} {a'} e z rewrite e = z


-- MOVE to mod
∀𝕎-□Func2 : {w : 𝕎·} {f g h : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e')
                       → □· w f
                       → □· w g
                       → □· w h
∀𝕎-□Func2 {w} {f} {g} {h} aw a b = Mod.□Func M (Mod.∀𝕎-□Func M aw a) b


-- MOVE to mod
∀𝕎-□Func3 : {w : 𝕎·} {f g h k : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e' → k w' e')
                       → □· w f
                       → □· w g
                       → □· w h
                       → □· w k
∀𝕎-□Func3 {w} {f} {g} {h} aw a b c = Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□Func M aw a) b) c



IFLE-steps₁ : {k : ℕ} {w w' : 𝕎·} {n m a u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLE a n u v , w) ≡ (IFLE a m u v , w'))
IFLE-steps₁ {0} {w} {w'} {n} {m} {a} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLE-steps₁ {suc k} {w} {w'} {n} {m} {a} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT n a v u , w) ≡ (IFLT m a v u , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLE-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLE⇓₁ : {w w' : 𝕎·} {n m a u v : Term}
         → n ⇓ m from w to w'
         → IFLE a n u v ⇓ IFLE a m u v from w to w'
IFLE⇓₁ {w} {w'} {n} {m} {a} {u} {v} (k , comp) = IFLE-steps₁ {k} {w} {w'} {n} {m} {a} {u} {v} comp


IFLE⇛₁ : {w : 𝕎·} {n m a u v : Term}
         → n ⇛ m at w
         → IFLE a n u v ⇛ IFLE a m u v at w
IFLE⇛₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLE⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLE-steps₂ : {k : ℕ} {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLE n (NUM i) u v , w) ≡ (IFLE m (NUM i) u v , w'))
IFLE-steps₂ {0} {w} {w'} {i} {n} {m} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLE-steps₂ {suc k} {w} {w'} {i} {n} {m} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT (NUM i) n v u , w) ≡ (IFLT (NUM i) m v u , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLE-steps₂ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLE⇓₂ : {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇓ m from w to w'
         → IFLE n (NUM i) u v ⇓ IFLE m (NUM i) u v from w to w'
IFLE⇓₂ {w} {w'} {i} {n} {m} {u} {v} (k , comp) = IFLE-steps₂ {k} {w} {w'} {i} {n} {m} {u} {v} comp


IFLE⇛₂ : {w : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇛ m at w
         → IFLE n (NUM i) u v ⇛ IFLE m (NUM i) u v at w
IFLE⇛₂ {w} {i} {n} {m} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLE⇓₂ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLE⇛≤ : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → k ≤ j
          → IFLE (NUM k) (NUM j) a b ⇛ a at w
IFLE⇛≤ {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLE (NUM k) (NUM j) a b) w1 ≡ a
    c with j <? k
    ... | yes p = ⊥-elim (1+n≰n (≤-trans p lekj))
    ... | no p = refl


IFLE⇛¬≤ : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → ¬ k ≤ j
          → IFLE (NUM k) (NUM j) a b ⇛ b at w
IFLE⇛¬≤ {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLE (NUM k) (NUM j) a b) w1 ≡ b
    c with j <? k
    ... | yes p = refl
    ... | no p = ⊥-elim (n≮n j z4)
      where
        z1 : k < suc j
        z1 = ≰⇒> p

        z2 : j < k
        z2 = ≰⇒> lekj

        z3 : k ≡ j
        z3 = <s→¬<→≡ z1 (≤⇒≯ (<⇒≤ z2))

        z4 : j < j
        z4 = <-transˡ z2 (≤-reflexive z3)


CHOOSE-NAME⇛AX : {w : 𝕎·} {name : Name} {t : Term} → CHOOSE (NAME name) t ⇛ AX at w
CHOOSE-NAME⇛AX {w} {name} {t} w1 e1 = lift (1 , refl)


#CHOOSE-NAME⇛AX : {w : 𝕎·} {name : Name} {t : CTerm} → #CHOOSE (#NAME name) t #⇛ #AX at w
#CHOOSE-NAME⇛AX {w} {name} {t} w1 e1 = CHOOSE-NAME⇛AX w1 e1


-- MOVE to computation
IFLE-CHOOSE⇛AX : {w : 𝕎·} {n a : Term} {k j : ℕ} {name : Name} {t : Term}
                  → n ⇛ NUM k at w
                  → a ⇛ NUM j at w
                  → IFLE n a (CHOOSE (NAME name) t) AX ⇛ AX at w
IFLE-CHOOSE⇛AX {w} {n} {a} {k} {j} {name} {t} c d =
  ⇛-trans (IFLE⇛₁ d) (⇛-trans (IFLE⇛₂ c) concl)
  where
    concl : IFLE (NUM k) (NUM j) (CHOOSE (NAME name) t) AX ⇛ AX at w
    concl with k ≤? j
    ... | yes p = ⇛-trans (IFLE⇛≤ p) CHOOSE-NAME⇛AX
    ... | no p = IFLE⇛¬≤ p


SEQ-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (SEQ a t , w) ≡ (SEQ b t , w'))
SEQ-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
SEQ-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (SEQ a t , w) ≡ (SEQ b t , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = SEQ-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


SEQ⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → SEQ a t ⇓ SEQ b t from w to w'
SEQ⇓₁ {w} {w'} {a} {b} {t} (k , comp) = SEQ-steps₁ {k} {w} {w'} {a} {b} {t} comp



SEQ⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → SEQ a b ⇛ SEQ a' b at w
SEQ⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (SEQ⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))



SEQ-val⇓₁from-to : {w : 𝕎·} {a t : Term} → # t → isValue a → SEQ a t ⇓ t from w to w
SEQ-val⇓₁from-to {w} {a} {t} tc isv = 1 , c
  where
    c : steps 1 (SEQ a t , w) ≡ (t , w)
    c with isValue⊎ a
    ... | inj₁ x rewrite #shiftUp 0 (ct t tc) | subNotIn a t tc = refl
    ... | inj₂ x = ⊥-elim (x isv)


SEQ-AX⇓₁from-to : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇓ t from w to w
SEQ-AX⇓₁from-to {w} {t} tc = SEQ-val⇓₁from-to {w} {AX} {t} tc tt


SEQ-AX⇓₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇓ t at w
SEQ-AX⇓₁ {w} {t} tc = 1 , c
  where
    c : sub AX (shiftUp 0 t) ≡ t
    c rewrite #shiftUp 0 (ct t tc) | subNotIn AX t tc = refl


SEQ-AX⇛₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇛ t at w
SEQ-AX⇛₁ {w} {t} tc w1 e1 = lift (SEQ-AX⇓₁ tc)


SEQ-AX⇛ : {w : 𝕎·} {a b : Term}
           → # b
           → a ⇛ AX at w
           → SEQ a b ⇛ b at w
SEQ-AX⇛ {w} {a} {b} cb comp = ⇛-trans (SEQ⇛₁ comp) (SEQ-AX⇛₁ cb)


bound∈ : (i : ℕ) (w : 𝕎·) (name : Name) (n : CTerm) (f : CTerm)
         → ∈Type i w #NAT n
         → ∈Type i w #BAIRE f
         → ∈Type i w #BAIRE (#bound name n f)
bound∈ i w name n f ∈n ∈f =
  ≡CTerm→equalInTypeₗ (sym (#bound≡ name n f)) (≡CTerm→equalInTypeᵣ (sym (#bound≡ name n f)) (≡CTerm→equalInType (sym #BAIRE≡) eqi))
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY (#BOUND name n f) a₁) (#APPLY (#BOUND name n f) a₂))
    aw w1 e1 a₁ a₂ ea = equalInType-#⇛-LR-rev (#⇛!-#APPLY-#BOUND w1 name n f a₁) (#⇛!-#APPLY-#BOUND w1 name n f a₂) eqi1
      where
        eqa : □· w1 (λ w' _ → NATeq w' a₁ a₂)
        eqa = equalInType-NAT→ i w1 a₁ a₂ ea

        eqn : □· w1 (λ w' _ → NATeq w' n n)
        eqn = equalInType-NAT→ i w1 n n (equalInType-mon ∈n w1 e1)

        eqf : □· w1 (λ w' _ → NATeq w' (#APPLY f a₁) (#APPLY f a₂))
        eqf = equalInType-NAT→ i w1 (#APPLY f a₁) (#APPLY f a₂) (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ (equalInType-mon ∈f w1 e1)) w1 (⊑-refl· _) a₁ a₂ ea)

        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂
                             → NATeq w' n n
                             → NATeq w' (#APPLY f a₁) (#APPLY f a₂)
                             → NATeq w' (#SEQ (#IFLE n a₁ (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₁))
                                         (#SEQ (#IFLE n a₂ (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₂)))
        aw1 w2 e2 (j , c₁ , c₂) (k , d₁ , d₂) (m , e₁ , e₂) =
          m ,
          ⇛-trans (SEQ-AX⇛ (CTerm.closed (#APPLY f a₁)) (IFLE-CHOOSE⇛AX d₁ c₁)) e₁ ,
          ⇛-trans (SEQ-AX⇛ (CTerm.closed (#APPLY f a₂)) (IFLE-CHOOSE⇛AX d₂ c₂)) e₂

        eqi1 : equalInType i w1 #NAT (#SEQ (#IFLE n a₁ (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₁))
                                     (#SEQ (#IFLE n a₂ (#CHOOSE (#NAME name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₂))
        eqi1 = →equalInType-NAT i w1 _ _ (∀𝕎-□Func3 aw1 eqa eqn eqf)

    eqi : equalInType i w (#FUN #NAT #NAT) (#BOUND name n f) (#BOUND name n f)
    eqi = equalInType-FUN (λ w1 e1 → eqTypesNAT) (λ w1 e1 → eqTypesNAT) aw



APPLY-bound∈ : (i : ℕ) (w : 𝕎·) (F : CTerm) (name : Name) (n : CTerm) (f : CTerm)
               → ∈Type i w #BAIRE→NAT F
               → ∈Type i w #NAT n
               → ∈Type i w #BAIRE f
               → ∈Type i w #NAT (#APPLY F (#bound name n f))
APPLY-bound∈ i w F name n f ∈F ∈n ∈f =
  equalInType-FUN→
    {i} {w} {#BAIRE} {#NAT} {F} {F} ∈F w (⊑-refl· _) (#bound name n f) (#bound name n f)
    (bound∈ i w name n f ∈n ∈f)



-- MOVE to props3
→INL-equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B x y : CTerm}
                          → isType n w B
                          → equalInType n w A x y
                          → equalInType n w (#UNION A B) (#INL x) (#INL y)
→INL-equalInType-UNION {n} {w} {A} {B} {x} {y} tb h =
  →equalInType-UNION (fst h) tb (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → Σ CTerm (λ x₁ → Σ CTerm (λ y₁ →
               #INL x #⇛ #INL x₁ at w' × #INL y #⇛ #INL y₁ at w' × equalInType n w' A x₁ y₁
               ⊎ #INL x #⇛ #INR x₁ at w' × #INL y #⇛ #INR y₁ at w' × equalInType n w' B x₁ y₁)))
    aw w' e' = x , y , inj₁ (#compAllRefl (#INL x) w' , #compAllRefl (#INL y) w' , equalInType-mon h w' e')


-- MOVE to props3
→INR-equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B x y : CTerm}
                          → isType n w A
                          → equalInType n w B x y
                          → equalInType n w (#UNION A B) (#INR x) (#INR y)
→INR-equalInType-UNION {n} {w} {A} {B} {x} {y} ta h =
  →equalInType-UNION ta (fst h) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → Σ CTerm (λ x₁ → Σ CTerm (λ y₁ →
               #INR x #⇛ #INL x₁ at w' × #INR y #⇛ #INL y₁ at w' × equalInType n w' A x₁ y₁
               ⊎ #INR x #⇛ #INR x₁ at w' × #INR y #⇛ #INR y₁ at w' × equalInType n w' B x₁ y₁)))
    aw w' e' = x , y , inj₂ (#compAllRefl (#INR x) w' , #compAllRefl (#INR y) w' , equalInType-mon h w' e')



{--
-- MOVE to props3
→equalInType-QTUNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓! (#INL x) at w' × b #⇓! (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓! (#INR x) at w' × b #⇓! (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#TSQUASH (#UNION A B)) a b
→equalInType-QTUNION {n} {w} {A} {B} {a} {b} isa isb i =
  equalInTypeTSQUASH← (Mod.∀𝕎-□Func M aw ({--Mod.→□∀𝕎 M--} i))
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇓! #INL x at w' × b #⇓! #INL y at w' × equalInType n w' A x y ⊎
                            a #⇓! #INR x at w' × b #⇓! #INR y at w' × equalInType n w' B x y))
                        → TSQUASHeq (equalInType n w' (#UNION A B)) w' a b)
    aw w' e' (x , y , inj₁ (c₁ , c₂ , h)) = TSQUASH-eq→ (TSQUASH-eq-base (#INL x) (#INL y) tt tt (#⇓!→∼C! {w'} {a} {#INL x} c₁) (#⇓!→∼C! {w'} {b} {#INL y} c₂) (→INL-equalInType-UNION (eqTypes-mon (uni n) isb w' e') h))
    aw w' e' (x , y , inj₂ (c₁ , c₂ , h)) = TSQUASH-eq→ (TSQUASH-eq-base (#INR x) (#INR y) tt tt (#⇓!→∼C! {w'} {a} {#INR x} c₁) (#⇓!→∼C! {w'} {b} {#INR y} c₂) (→INR-equalInType-UNION (eqTypes-mon (uni n) isa w' e') h))
--}



{--
-- MOVE to props3
→equalInType-TRUNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#TTRUNC (#UNION A B)) a b
→equalInType-TRUNION {n} {w} {A} {B} {a} {b} isa isb i =
  equalInTypeTTRUNC← (Mod.∀𝕎-□Func M aw ({--Mod.→□∀𝕎 M--} i))
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇓ #INL x at w' × b #⇓ #INL y at w' × equalInType n w' A x y ⊎
                            a #⇓ #INR x at w' × b #⇓ #INR y at w' × equalInType n w' B x y))
                        → TTRUNCeq (equalInType n w' (#UNION A B)) w' a b)
    aw w' e' (x , y , inj₁ (c₁ , c₂ , h)) =
      TTRUNC-eq→ (TTRUNC-eq-base
                    (#INL x) (#INL y) tt tt c₁ c₂
                    (→INL-equalInType-UNION (eqTypes-mon (uni n) isb w' e') h))
    aw w' e' (x , y , inj₂ (c₁ , c₂ , h)) =
      TTRUNC-eq→ (TTRUNC-eq-base
                    (#INR x) (#INR y) tt tt c₁ c₂
                    (→INR-equalInType-UNION (eqTypes-mon (uni n) isa w' e') h))
--}



{--
-- MOVE to props3
TTRUNC-eq-UNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                    → TTRUNC-eq (equalInType n w (#UNION A B)) w a b
                    → Σ CTerm (λ x → Σ CTerm (λ y →
                           a #⇓ #INL x at w × b #⇓ #INL y at w × equalInType n w A x y ⊎
                           a #⇓ #INR x at w × b #⇓ #INR y at w × equalInType n w B x y))
TTRUNC-eq-UNION→ {n} {w} {A} {B} {a} {b} (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) = {!!} --Mod.□-const M (Mod.∀𝕎-□Func M aw eqi)
  where
    eqi : □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                          → (a1 #⇛ (#INL x) at w' × a2 #⇛ (#INL y) at w' × equalInType n w' A x y)
                             ⊎ (a1 #⇛ (#INR x) at w' × a2 #⇛ (#INR y) at w' × equalInType n w' B x y))))
    eqi = equalInType-UNION→ ea

    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                           a1 #⇛ #INL x at w' × a2 #⇛ #INL y at w' × equalInType n w' A x y ⊎
                           a1 #⇛ #INR x at w' × a2 #⇛ #INR y at w' × equalInType n w' B x y))
                       → Σ CTerm (λ x → Σ CTerm (λ y →
                           a #⇓ #INL x at w × b #⇓ #INL y at w × equalInType n w A x y ⊎
                           a #⇓ #INR x at w × b #⇓ #INR y at w × equalInType n w B x y)))
    aw w' e' (x , y , inj₁ (c₁ , c₂ , eqa)) =
      x , y , inj₁ (≡R→#⇓ (#⇛→≡ c₁ i1) c1 ,
                    ≡R→#⇓ (#⇛→≡ c₂ i2) c2 ,
                    equalInType-local (Mod.∀𝕎-□Func M aw' eqi))
      where
        aw' : ∀𝕎 w (λ w'' e'' → Σ CTerm (λ x₁ → Σ CTerm (λ y₁ →
                                   a1 #⇛ #INL x₁ at w'' × a2 #⇛ #INL y₁ at w'' × equalInType n w'' A x₁ y₁
                                   ⊎ a1 #⇛ #INR x₁ at w'' × a2 #⇛ #INR y₁ at w'' × equalInType n w'' B x₁ y₁))
                              → equalInType n w'' A x y)
        aw' w'' e'' (x₁ , y₁ , inj₁ (d₁ , d₂ , eqa')) = {!!}
        aw' w'' e'' (x₁ , y₁ , inj₂ (d₁ , d₂ , eqb')) = {!!}
    aw w' e' (x , y , inj₂ (c₁ , c₂ , eqb)) = {!!}

TTRUNC-eq-UNION→ {n} {w} {A} {B} {a} {b} (TTRUNC-eq-trans t h1 h2) = {!!}
--}



{--
-- MOVE to props3
equalInType-TRUNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#TTRUNC (#UNION A B)) a b
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
equalInType-TRUNION→ {n} {w} {A} {B} {a} {b} i = Mod.∀𝕎-□Func M {!!} j
  where
    j : □· w (λ w' _ → TTRUNCeq (equalInType n w' (#UNION A B)) w' a b)
    j = equalInTypeTTRUNC→ i

    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalInType n w' (#UNION A B)) w' a b
                       → Σ CTerm (λ x → Σ CTerm (λ y →
                           a #⇓ #INL x at w' × b #⇓ #INL y at w' × equalInType n w' A x y ⊎
                           a #⇓ #INR x at w' × b #⇓ #INR y at w' × equalInType n w' B x y)))
    aw w' e' h = {!!}
--}



{--
-- MOVE to terms
QTUNION : Term → Term → Term
QTUNION a b = TSQUASH (UNION a b)


-- MOVE to terms
#QTUNION : CTerm → CTerm → CTerm
#QTUNION a b = ct (QTUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # UNION ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#QTUNION≡ : (a b : CTerm) → #QTUNION a b ≡ #TSQUASH (#UNION a b)
#QTUNION≡ a b = CTerm≡ refl
--}



LET-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (LET a t , w) ≡ (LET b t , w'))
LET-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
LET-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (LET a t , w) ≡ (LET b t , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = LET-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


LET⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → LET a t ⇓ LET b t from w to w'
LET⇓₁ {w} {w'} {a} {b} {t} (k , comp) = LET-steps₁ {k} {w} {w'} {a} {b} {t} comp



LET⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → LET a b ⇛ LET a' b at w
LET⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (LET⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


isValue→LET⇓from-to : {v t : Term} {w : 𝕎·}
                       → isValue v
                       → LET v t ⇓ sub v t from w to w
isValue→LET⇓from-to {v} {t} {w} isv = 1 , c
  where
    c : steps 1 (LET v t , w) ≡ (sub v t , w)
    c with isValue⊎ v
    ... | inj₁ x = refl
    ... | inj₂ x = ⊥-elim (x isv)


isValue→LET⇛ : {v t : Term} {w : 𝕎·}
                 → isValue v
                 → LET v t ⇛ sub v t at w
isValue→LET⇛ {v} {t} {w} isv w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} {LET v t} {sub v t} (isValue→LET⇓from-to isv))


sub-num-probe-body : {m : ℕ} {name : Name}
                     → sub (NUM m) (IFLT (get0 name) (NUM 1) (INL (VAR 0)) (INR AX))
                        ≡ IFLT (get0 name) (NUM 1) (INL (NUM m)) (INR AX)
sub-num-probe-body {m} {name} = refl


≡ₗ→⇓from-to : {a b c : Term} {w1 w2 : 𝕎·}
              → c ≡ a
              → c ⇓ b from w1 to w2
              → a ⇓ b from w1 to w2
≡ₗ→⇓from-to {a} {b} {c} {w1} {w2} e comp rewrite e = comp



{--
IFC0-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t u : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (IFC0 a t u , w) ≡ (IFC0 b t u , w'))
IFC0-steps₁ {0} {w} {w'} {a} {b} {t} {u} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFC0-steps₁ {suc k} {w} {w'} {a} {b} {t} {u} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFC0 a t u , w) ≡ (IFC0 b t u , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = IFC0-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFC0⇓₁ : {w w' : 𝕎·} {a b t u : Term}
         → a ⇓ b from w to w'
         → IFC0 a t u ⇓ IFC0 b t u from w to w'
IFC0⇓₁ {w} {w'} {a} {b} {t} {u} (k , comp) = IFC0-steps₁ {k} {w} {w'} {a} {b} {t} {u} comp
--}


getChoice→getT : {n : ℕ} {name : Name} {w : 𝕎·} {c : ℂ·}
                  → getChoice· n name w ≡ just c
                  → getT n name w ≡ just ⌜ ℂ→C· c ⌝
getChoice→getT {n} {name} {w} {c} getc rewrite getc = refl



{--
IFC0-ℂ₀⇓from-to : {a b : Term} {w : 𝕎·}
                  → IFC0 ⌜ Cℂ₀ ⌝ a b ⇓ a from w to w
IFC0-ℂ₀⇓from-to {a} {b} {w} = 1 , c
  where
    c : steps 1 (IFC0 ⌜ Cℂ₀ ⌝ a b , w) ≡ (a , w)
    c with isValue⊎ ⌜ Cℂ₀ ⌝
    ... | inj₁ x with decT₀ ⌜ Cℂ₀ ⌝
    ... |    inj₁ y = refl
    ... |    inj₂ y = ⊥-elim (y ℂ₉→T→ℂ₀·)
    c | inj₂ x = ⊥-elim (x isValueℂ₀·)
--}


≡ℂ→≡ℂ→C : {a b : ℂ·}
             → a ≡ b
             → ℂ→C· a ≡ ℂ→C· b
≡ℂ→≡ℂ→C {a} {b} e rewrite e = refl


{--
IFC0-ℂ₁⇓from-to : {a b : Term} {w : 𝕎·}
                  → IFC0 ⌜ Cℂ₁ ⌝ a b ⇓ b from w to w
IFC0-ℂ₁⇓from-to {a} {b} {w} = 1 , c
  where
    c : steps 1 (IFC0 ⌜ Cℂ₁ ⌝ a b , w) ≡ (b , w)
    c with isValue⊎ ⌜ Cℂ₁ ⌝
    ... | inj₁ x with decT₀ ⌜ Cℂ₁ ⌝
    ... |    inj₁ y = ⊥-elim (¬∼ℂ₀₁· w (∼C!-sym {w} {Cℂ₁} {Cℂ₀} (≡R→∼C! {w} {Cℂ₁} {ℂ→C· (T→ℂ· ⌜ Cℂ₁ ⌝)} {Cℂ₀}
                                                                          (≡ℂ→≡ℂ→C y)
                                                                          (≡R→∼C! {w} {Cℂ₁} {Cℂ₁} {_} (≡ℂ→≡ℂ→C (sym ℂ₁→T→ℂ₁·)) (∼C!-refl {w} {Cℂ₁}))))) --refl
    ... |    inj₂ y = refl --⊥-elim (y ℂ₉→T→ℂ₀·)
    c | inj₂ x = ⊥-elim (x isValueℂ₁·)
--}


{--
probeℂ₀⇓ : {F n f : Term} {name : Name} {m : ℕ} {w1 w2 : 𝕎·}
           → APPLY F (bound name n f) ⇓ NUM m from w1 to w2
           → getChoice· 0 name w2 ≡ just ℂ₀·
           → probe name F n f ⇓ INL (NUM m) from w1 to w2
probeℂ₀⇓ {F} {n} {f} {name} {m} {w1} {w2} comp1 comp2 =
  ⇓-trans₂ (LET⇓₁ comp1)
           (⇓-trans₂ (isValue→LET⇓from-to tt)
                     (≡ₗ→⇓from-to (sym sub-num-probe-body)
                                  (⇓-trans₂ (IFC0⇓₁ (Σ-steps-APPLY-CS 0 (NUM 0) Tℂ₀ w2 w2 0 name refl (getChoice→getT comp2)))
                                            IFC0-ℂ₀⇓from-to)))
--}


{--
probeℂ₁⇓ : {F n f : Term} {name : Name} {m : ℕ} {w1 w2 : 𝕎·}
           → APPLY F (bound name n f) ⇓ NUM m from w1 to w2
           → getChoice· 0 name w2 ≡ just ℂ₁·
           → probe name F n f ⇓ INR AX from w1 to w2
probeℂ₁⇓ {F} {n} {f} {name} {m} {w1} {w2} comp1 comp2 =
  ⇓-trans₂ (LET⇓₁ comp1)
           (⇓-trans₂ (isValue→LET⇓from-to tt)
                     (≡ₗ→⇓from-to (sym sub-num-probe-body)
                                  (⇓-trans₂ (IFC0⇓₁ (Σ-steps-APPLY-CS 0 (NUM 0) Tℂ₁ w2 w2 0 name refl (getChoice→getT comp2)))
                                            IFC0-ℂ₁⇓from-to)))
--}



{--
-- To prove this with UNION instead of QTUNION, we would have to assume ¬read of 'F', 'n', and 'f', so that 'test' computes
-- to the same value in all extensions of the current world
-- We also have to assume that 'F', 'n', and 'f' do not write to name
test∈ : (i : ℕ) (w : 𝕎·) (F : CTerm) (name : Name) (n : CTerm) (f : CTerm)
        → compatible· name w Resℂ₀₁
        → ∈Type i w #BAIRE→NAT F
        → ∈Type i w #NAT n
        → ∈Type i w #BAIRE f
        → ∈Type i w (#QTUNION #NAT #TRUE) (#test name F n f)
test∈ i w F name n f compat ∈F ∈n ∈f =
{--  ≡CTerm→equalInType
    (sym (#UNION≡ Typeℂ₀₁· #TRUE))--}
    (→equalInType-QTUNION eqTypesNAT eqTypesTRUE (∀𝕎-□Func2 aw gc ∈A))
  where
    ∈A : □· w (λ w' _ → NATeq w' (#APPLY F (#bound name n f)) (#APPLY F (#bound name n f)))
    ∈A = equalInType-NAT→ i w (#APPLY F (#bound name n f)) (#APPLY F (#bound name n f)) (APPLY-bound∈ i w F name n f ∈F ∈n ∈f)

    gc : □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (getChoice· 0 name w'' ≡ just ℂ₀· ⊎ getChoice· 0 name w'' ≡ just ℂ₁·)))
    gc = Mod.∀𝕎-□Func M gcaw (□·-choice· w name 0 Resℂ₀₁ compat)
      where
        gcaw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (λ w'' _ → Lift (lsuc L) (Σ ℂ· (λ t → getChoice· 0 name w'' ≡ just t × ·ᵣ Resℂ₀₁ 0 t)))
                              → ∀𝕎 w' (λ w'' _ → Lift (lsuc L) (getChoice· 0 name w'' ≡ just ℂ₀· ⊎ getChoice· 0 name w'' ≡ just ℂ₁·)))
        gcaw w1 e1 h w2 e2 = lift (gcj (lower (h w2 e2)))
          where
            gcj : Σ ℂ· (λ t → getChoice· 0 name w2 ≡ just t × ·ᵣ Resℂ₀₁ 0 t) → getChoice· 0 name w2 ≡ just ℂ₀· ⊎ getChoice· 0 name w2 ≡ just ℂ₁·
            gcj (t , gct , inj₁ z) rewrite z = inj₁ gct
            gcj (t , gct , inj₂ z) rewrite z = inj₂ gct

    aw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (getChoice· 0 name w'' ≡ just ℂ₀· ⊎ getChoice· 0 name w'' ≡ just ℂ₁·))
                        → NATeq w' (#APPLY F (#bound name n f)) (#APPLY F (#bound name n f))
                        → Σ CTerm (λ x → Σ CTerm (λ y →
                            #test name F n f #⇓ #INL x at w' × #test name F n f #⇓ #INL y at w' × equalInType i w' #NAT x y
                            ⊎ #test name F n f #⇓ #INR x at w' × #test name F n f #⇓ #INR y at w' × equalInType i w' #TRUE x y)))
    aw w1 e1 gcn (m , c₁ , c₂) = j (lower (gcn w3 (⊑-trans· e2 e3)))
      where
        comp1 : Σ 𝕎· (λ w2 → #set name #⇓ #AX from w1 to w2)
        comp1 = #⇛→#⇓from-to {w1} {#set name} {#AX} (#CHOOSE-NAME⇛AX {w1} {name} {ℂ→C· ℂ₀·})

        w2 : 𝕎·
        w2 = fst comp1

        comp1' : #set name #⇓ #AX from w1 to w2
        comp1' = snd comp1

        e2 : w1 ⊑· w2
        e2 = #⇓from-to→⊑ {_} {_} {#set name} {#AX} comp1'

        comp2 : Σ 𝕎· (λ w3 → #APPLY F (#bound name n f) #⇓ #NUM m from w2 to w3)
        comp2 = #⇛→#⇓from-to {w2} {#APPLY F (#bound name n f)} {#NUM m} (∀𝕎-mon e2 c₁)

        w3 : 𝕎·
        w3 = fst comp2

        comp2' : (#APPLY F (#bound name n f)) #⇓ (#NUM m) from w2 to w3
        comp2' = snd comp2

        e3 : w2 ⊑· w3
        e3 = #⇓from-to→⊑ {_} {_} {#APPLY F (#bound name n f)} {#NUM m} comp2'

        j : (getChoice· 0 name w3 ≡ just ℂ₀· ⊎ getChoice· 0 name w3 ≡ just ℂ₁·)
            → Σ CTerm (λ x → Σ CTerm (λ y →
                  #test name F n f #⇓ #INL x at w1 × #test name F n f #⇓ #INL y at w1 × equalInType i w1 #NAT x y
                  ⊎ #test name F n f #⇓ #INR x at w1 × #test name F n f #⇓ #INR y at w1 × equalInType i w1 #TRUE x y))
        j (inj₁ z) = #NUM m , #NUM m , inj₁ (#⇓from-to→#⇓ {_} {_} {#test name F n f} {#INL (#NUM m)} comp4 ,
                                             #⇓from-to→#⇓ {_} {_} {#test name F n f} {#INL (#NUM m)} comp4 ,
                                             NUM-equalInType-NAT i w1 m)
          where
            comp3 : #probe name F n f #⇓ #INL (#NUM m) from w2 to w3
            comp3 = probeℂ₀⇓ comp2' z

            comp4 : #test name F n f #⇓ #INL (#NUM m) from w1 to w3
            comp4 = ⇓-trans₂ {w1} {w2} {w3} {_} {⌜ #SEQ #AX (#probe name F n f) ⌝} {_}
                             (SEQ⇓₁ {w1} {w2} {⌜ #set name ⌝} {AX} {⌜ #probe name F n f ⌝} comp1')
                             (⇓-trans₂ {w2} {w2} {w3} {_} {⌜ #probe name F n f ⌝} {_}
                                       (SEQ-AX⇓₁from-to (CTerm.closed (#probe name F n f)))
                                       comp3)

        j (inj₂ z) = #AX , #AX , inj₂ (#⇓from-to→#⇓ {_} {_} {#test name F n f} {#INR #AX} comp4 ,
                                       #⇓from-to→#⇓ {_} {_} {#test name F n f} {#INR #AX} comp4 ,
                                       →equalInType-TRUE i)
          where
            comp3 : #probe name F n f #⇓ #INR #AX from w2 to w3
            comp3 = probeℂ₁⇓ comp2' z

            comp4 : #test name F n f #⇓ #INR #AX from w1 to w3
            comp4 = ⇓-trans₂ {w1} {w2} {w3} {_} {⌜ #SEQ #AX (#probe name F n f) ⌝} {_}
                             (SEQ⇓₁ {w1} {w2} {⌜ #set name ⌝} {AX} {⌜ #probe name F n f ⌝} comp1')
                             (⇓-trans₂ {w2} {w2} {w3} {_} {⌜ #probe name F n f ⌝} {_}
                                       (SEQ-AX⇓₁from-to (CTerm.closed (#probe name F n f)))
                                       comp3)
--}


-- Prove this for the current world, and show that if F and f cannot read then this is true for all extensions too

-- Do we need to constrain F's type to be in (BAIRE→NAT!)? -- No, doesn't make sense: what function is going to inhabit that type?

-- Check what world (#APPLY F (#bound name n f)) ends up in and name's value in that world
-- and compare it with with ℂ₀ before instantiating the conclusion
-- Because we used NAT, this requires choices to be numbers (should be QTNAT in the union)


CTerm→CTerm0→Term : (a : CTerm) → ⌜ CTerm→CTerm0 a ⌝ ≡ ⌜ a ⌝
CTerm→CTerm0→Term (ct a c) = refl


CTerm→CTerm1→Term : (a : CTerm) → ⌜ CTerm→CTerm1 a ⌝ ≡ ⌜ a ⌝
CTerm→CTerm1→Term (ct a c) = refl



#⇛!-#APPLY-#UPD : (w : 𝕎·) (name : Name) (f : CTerm) (a : CTerm)
                   → #APPLY (#UPD name f) a #⇛! #LET a (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY ⌞ f ⌟ #[0]VAR)) at w
#⇛!-#APPLY-#UPD w name f a w1 e1
  = lift (1 , →≡pair (→sub-LET {⌜ a ⌝} {⌜ #[0]VAR ⌝} {⌜ #[1]SEQ (#[1]updGt name #[1]VAR0) (#[1]APPLY ⌞ f ⌟ #[1]VAR0) ⌝}
                                 (CTerm.closed a)
                                 (sub-VAR0 ⌜ a ⌝)
                                 (→≡LET refl (→≡APPLY e refl)))
                     refl)
  where
    e : shiftDown 2 (subv 2 (shiftUp 0 ⌜ a ⌝) (shiftUp 0 ⌜ CTerm→CTerm1 f ⌝))
        ≡ shiftUp 0 ⌜ CTerm→CTerm0 f ⌝
    e rewrite #shiftUp 0 a
            | CTerm→CTerm0→Term f
            | CTerm→CTerm1→Term f
            | #shiftUp 0 f
            | #subv 2 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f) = #shiftDown 2 f


{--
⇓-upd-body : (w : 𝕎·) (f a : Term) (m k : ℕ) (name : Name)
              → a ⇓ NUM m at w
              → APPLY f (NUM m) ⇛ NUM k at w
              → LET a (SEQ (CHOOSE (NAME name) (VAR 0)) (APPLY f (VAR 0))) ⇓ NUM k at w
⇓-upd-body w f a m k name c₁ c₂ = {!!}
--}


≡ₗ→⇛ : {a b c : Term} (w : 𝕎·) → a ≡ c → a ⇛ b at w → c ⇛ b at w
≡ₗ→⇛ {a} {b} {c} w e comp rewrite e = comp


→#-APPLY : {a b : Term} → # a → # b → # APPLY a b
→#-APPLY {a} {b} ca cb rewrite ca | cb = refl


→#[]-APPLY : {a b : Term} {l : List Var} → #[ l ] a → #[ l ] b → #[ l ] APPLY a b
→#[]-APPLY {a} {b} {l} ca cb =
  ⊆→⊆? {fvars a ++ fvars b } {l}
        (⊆++ (⊆?→⊆ {fvars a} {l} ca)
             (⊆?→⊆ {fvars b} {l} cb))


#→#[] : {a : Term} {l : List Var} → # a → #[ l ] a
#→#[] {a} {l} ca rewrite ca = refl


old-⇛-upd-body : (w : 𝕎·) (f a : Term) (m k : ℕ) (name : Name)
                  → # f
                  → a ⇛ NUM m at w
                  → APPLY f (NUM m) ⇛ NUM k at w
                  → LET a (SEQ (CHOOSE (NAME name) (VAR 0)) (APPLY f (VAR 0))) ⇛ NUM k at w
old-⇛-upd-body w f a m k name cf c₁ c₂ =
  ⇛-trans (LET⇛₁ c₁)
           (⇛-trans (isValue→LET⇛ tt)
                     (≡ₗ→⇛ w (sym (→sub-SEQ {NUM m} {CHOOSE (NAME name) (VAR 0)} {APPLY f (VAR 0)} {CHOOSE (NAME name) (NUM m)} {APPLY f (NUM m)}
                                              refl (→#[]-APPLY {f} {VAR 0} {[ 0 ]} (#→#[] {f} {[ 0 ]} cf) refl) refl (→sub-APPLY {NUM m} {f} {VAR 0} {f} {NUM m} (subNotIn (NUM m) f cf) refl)))
                              (⇛-trans (SEQ⇛₁ CHOOSE-NAME⇛AX)
                                        (⇛-trans (SEQ-AX⇛₁ (→#-APPLY {f} {NUM m} cf refl)) c₂))))



IFLT-NUM⇓< : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → n < m
              → step (IFLT (NUM n) (NUM m) a b) w ≡ just (a , w)
IFLT-NUM⇓< n m w a b ltnm with n <? m
... | yes r = refl
... | no r = ⊥-elim (r ltnm)


IFLT-NUM⇓¬< : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → ¬ (n < m)
              → step (IFLT (NUM n) (NUM m) a b) w ≡ just (b , w)
IFLT-NUM⇓¬< n m w a b ltnm with n <? m
... | yes r = ⊥-elim (ltnm r)
... | no r = refl


IFLT-NUM⇓ : (n m : ℕ) (w : 𝕎·) (a b c : Term)
              → a ⇓ c at w
              → b ⇓ c at w
              → IFLT (NUM n) (NUM m) a b ⇓ c at w
IFLT-NUM⇓ n m w a b c c₁ c₂ with n <? m
... | yes r = step-⇓-trans (IFLT-NUM⇓< n m w a b r) c₁
... | no r = step-⇓-trans (IFLT-NUM⇓¬< n m w a b r) c₂


updGt⇛AX : {w : 𝕎·} {name : Name} {m : ℕ}
            → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
            → updGt name (NUM m) ⇛ AX at w
updGt⇛AX {w} {name} {m} g0 w1 e1 =
  lift (step-⇓-trans s (IFLT-NUM⇓ (fst z) m w1 (setT name (NUM m)) AX AX (lower (CHOOSE-NAME⇛AX w1 (⊑-refl· _))) (⇓-refl AX w1)))
  where
    z : Σ ℕ (λ j → getT 0 name w1 ≡ just (NUM j))
    z = lower (g0 w1 e1)

    s : step (updGt name (NUM m)) w1 ≡ just (IFLT (NUM (fst z)) (NUM m) (setT name (NUM m)) AX , w1)
    s with is-NUM (get0 name)
    ... | inj₁ (n , ())
    ... | inj₂ p with step⊎ (get0 name) w1
    ... |    inj₁ (k , w' , q) rewrite q | snd z | pair-inj₁ (just-inj (sym q)) | pair-inj₂ (just-inj (sym q)) = refl
    ... |    inj₂ q rewrite q | snd z = ⊥-elim (¬just≡nothing q)


⇛-upd-body : (w : 𝕎·) (f a : Term) (m k : ℕ) (name : Name)
              → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
              → # f
              → a ⇛ NUM m at w
              → APPLY f (NUM m) ⇛ NUM k at w
              → LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) ⇛ NUM k at w
⇛-upd-body w f a m k name g0 cf c₁ c₂ =
  ⇛-trans (LET⇛₁ c₁)
           (⇛-trans (isValue→LET⇛ tt)
                     (≡ₗ→⇛ w (sym (→sub-SEQ {NUM m} {updGt name (VAR 0)} {APPLY f (VAR 0)} {updGt name (NUM m)} {APPLY f (NUM m)}
                                              refl (→#[]-APPLY {f} {VAR 0} {[ 0 ]} (#→#[] {f} {[ 0 ]} cf) refl)
                                              refl (→sub-APPLY {NUM m} {f} {VAR 0} {f} {NUM m} (subNotIn (NUM m) f cf) refl)))
                              (⇛-trans (SEQ⇛₁ (updGt⇛AX g0))
                                        (⇛-trans (SEQ-AX⇛₁ (→#-APPLY {f} {NUM m} cf refl)) c₂))))



upd∈ : (i : ℕ) (w : 𝕎·) (name : Name) (f : CTerm)
       → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
       → ∈Type i w #BAIRE f
       → ∈Type i w #BAIRE (#upd name f)
upd∈ i w name f g0 ∈f = ≡CTerm→∈Type (sym (#upd≡ name f)) (≡CTerm→equalInType (sym #BAIRE≡) eqi)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY (#UPD name f) a₁) (#APPLY (#UPD name f) a₂))
    aw w1 e1 a₁ a₂ ea =
      equalInType-#⇛-LR-rev
        (#⇛!-#APPLY-#UPD w1 name f a₁)
        (#⇛!-#APPLY-#UPD w1 name f a₂)
        eqi1
      where
        eqa : □· w1 (λ w' _ → NATeq w' a₁ a₂)
        eqa = equalInType-NAT→ i w1 a₁ a₂ ea

        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂
                              → Mod.□ M w' (↑wPred' (λ w'' _ → NATeq w''
                                   (#LET a₁ (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY (CTerm→CTerm0 f) #[0]VAR)))
                                   (#LET a₂ (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY (CTerm→CTerm0 f) #[0]VAR)))) e'))
        aw1 w2 e2 (m , c₁ , c₂) = Mod.∀𝕎-□Func M aw2 eqf
          where
            aw2 : ∀𝕎 w2 (λ w' e' → NATeq w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m))
                                 → ↑wPred' (λ w'' _ → NATeq w'' (#LET a₁ (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY (CTerm→CTerm0 f) #[0]VAR)))
                                                                 (#LET a₂ (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY (CTerm→CTerm0 f) #[0]VAR)))) e2 w' e')
            aw2 w3 e3 (k , d₁ , d₂) z =
              k ,
              ⇛-upd-body w3 ⌜ f ⌝ ⌜ a₁ ⌝ m k name (∀𝕎-mon (⊑-trans· e1 z) g0) (CTerm.closed f) (∀𝕎-mon e3 c₁) d₁ ,
              ⇛-upd-body w3 ⌜ f ⌝ ⌜ a₂ ⌝ m k name (∀𝕎-mon (⊑-trans· e1 z) g0) (CTerm.closed f) (∀𝕎-mon e3 c₂) d₂

            eqf : □· w2 (λ w' _ → NATeq w' (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
            eqf = equalInType-NAT→ i w2 (#APPLY f (#NUM m)) (#APPLY f (#NUM m)) (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) w2 (⊑-refl· _) (#NUM m) (#NUM m) (NUM-equalInType-NAT i w2 m))

        eqi1 : equalInType i w1 #NAT (#LET a₁ (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY ⌞ f ⌟ #[0]VAR)))
                                     (#LET a₂ (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY ⌞ f ⌟ #[0]VAR)))
        eqi1 = →equalInType-NAT i w1 _ _ (Mod.□-idem M (Mod.∀𝕎-□Func M aw1 eqa))

    eqi : ∈Type i w (#FUN #NAT #NAT) (#UPD name f)
    eqi = equalInType-FUN (λ w1 e1 → eqTypesNAT) (λ w1 e1 → eqTypesNAT) aw


{--
probeM-NAT : (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → ∈Type i w #NAT (#probeM name F f)
probeM-NAT i w name F f ∈F ∈f = ≡CTerm→∈Type (sym (#probeM≡ name F f)) {!!}
  where
    eqa : ∈Type i w #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→ ∈F w (⊑-refl· _) (#upd name f) (#upd name f) (upd∈ i w name f ∈f)
--}



record ℕℂ : Set₁ where
  constructor mkℕℂ
  field
    ncC : (c : ℂ·) → Σ ℕ (λ m → ℂ→T c ≡ NUM m)
    ncN : (n : ℕ) → ℂ→C· (T→ℂ· (NUM n)) ≡ #NUM n


-- Move to ?
-- This is Res⊤ where when ℂ is ℕ essentially
Resℕ : ℕℂ → Res
Resℕ nc = mkRes (λ n t → Σ ℕ (λ m → ℂ→T t ≡ NUM m)) (T→ℂ· (NUM 0)) (λ n → 0 , e) (true , c1) (true , c2)
  where
    e : ℂ→T (T→ℂ· (NUM 0)) ≡ NUM 0
    e rewrite ℕℂ.ncN nc 0 = refl

    c1 : (n : ℕ) (c : ℂ·) → Σ ℕ (λ m → ℂ→T c ≡ NUM m) ⊎ ¬ Σ ℕ (λ m → ℂ→T c ≡ NUM m)
    c1 n c = inj₁ (ℕℂ.ncC nc c)

    c2 : (n m : ℕ) (c : ℂ·) → Σ ℕ (λ k → ℂ→T c ≡ NUM k) → Σ ℕ (λ k → ℂ→T c ≡ NUM k)
    c2 n m c z = z


get-choose-ℕ : ℕℂ → Set(L)
get-choose-ℕ nc =
  (name : Name) (w : 𝕎·) (n : ℕ)
  → compatible· name w (Resℕ nc)
  → getT 0 name (chooseT name w (NUM n)) ≡ just (NUM n) -- Here only the 0th position is used


-- MOVE to computation
⇛→⇓from-to : {w : 𝕎·} {a b : Term}
                 → a ⇛ b at w
                 → Σ 𝕎· (λ w' → a ⇓ b from w to w')
⇛→⇓from-to {w} {a} {b} comp = ⇓→from-to (lower (comp w (⊑-refl· _)))


{--
¬read-upd≡ : (name : Name) (f : Term) → ¬read (upd name f) ≡ ¬read f
¬read-upd≡ name f = {!refl!}
--}


∀𝕎-getT0-NUM→∀𝕎get0-NUM : (w : 𝕎·) (name : Name)
                             → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
                             → ∀𝕎 w (λ w' e → Lift {L} (lsuc(L)) (Σ ℕ (λ k → get0 name ⇓ NUM k from w' to w')))
∀𝕎-getT0-NUM→∀𝕎get0-NUM w name h w1 e1 = lift (fst z , 1 , s)
  where
    z : Σ ℕ (λ j → getT 0 name w1 ≡ just (NUM j))
    z = lower (h w1 e1)

    s : steps 1 (get0 name , w1) ≡ (NUM (fst z) , w1)
    s rewrite snd z = refl


⇓from-to→⊑ : {w w' : 𝕎·} {a b : Term}
               → a ⇓ b from w to w'
               → w ⊑· w'
⇓from-to→⊑ {w} {w'} {a} {b} (n , comp) = ≡ᵣ→⊑ (steps⊑ w n a) (→≡snd comp)


comp→∀ℕ : Set(lsuc(L))
comp→∀ℕ = (nc : ℕℂ) (name : Name) (w : 𝕎·) (k : ℕ)
            → compatible· name w Res⊤
            → ∀𝕎 (chooseT name w (NUM k)) (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))


-- The modality is Kripke-like
K□ : Set(lsuc(lsuc(L)))
K□ = {w : 𝕎·} {f : wPred w} → □· w f → ∀𝕎 w f



-- TODO: now we ned to prove that testM computes to the same number in all extensions of w
-- (as long as name does not occur in F or f)
⇓APPLY-upd→⇓testM : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
                     → ∈Type i w #BAIRE→NAT F
                     → ∈Type i w #BAIRE f
                     → compatible· name w Res⊤
                     → Σ ℕ (λ k → testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM k at w)
⇓APPLY-upd→⇓testM nc cn kb i w name F f ∈F ∈f {--nrF nrf gcn--} comp =
  fst cg , ⇓-from-to→⇓ {w} {fst ca} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (fst cg)}
                       (⇓-trans₂ {w} {chooseT name w (NUM 0)} {fst ca} {testM name ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {NUM (fst cg)}
                                 (SEQ⇓₁ {w} {chooseT name w (NUM 0)} {set0 name} {AX} {probeM name ⌜ F ⌝ ⌜ f ⌝} cs)
                                 (⇓-trans₂ {chooseT name w (NUM 0)} {chooseT name w (NUM 0)} {fst ca} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {probeM name ⌜ F ⌝ ⌜ f ⌝} {NUM (fst cg)}
                                           (SEQ-AX⇓₁from-to (CTerm.closed (#probeM name F f)))
                                           (⇓-trans₂ {chooseT name w (NUM 0)} {fst ca} {fst ca} {probeM name ⌜ F ⌝ ⌜ f ⌝} {SEQ (NUM m) (get0 name)} {NUM (fst cg)}
                                                     (SEQ⇓₁ (snd ca))
                                                     (⇓-trans₂ {proj₁ ca} {proj₁ ca} {proj₁ ca} {SEQ (NUM m) (get0 name)} {get0 name} {NUM (proj₁ cg)}
                                                               (SEQ-val⇓₁from-to refl tt)
                                                               (snd cg)))))
  where
    w1 : 𝕎·
    w1 = chooseT name w (NUM 0)

    cs : set0 name ⇓ AX from w to w1
    cs = 1 , refl

    e1 : w ⊑· w1
    e1 = ⇓from-to→⊑ {w} {w1} cs

    g0 : ∀𝕎 w1 (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
    g0 = cn nc name w 0 comp

    eqa : ∈Type i w1 #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→
            (equalInType-mon ∈F w1 e1) w1 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w1 name f (cn nc name w 0 comp) (equalInType-mon ∈f w1 e1))

    eqn : NATeq w1 (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
    eqn = kb (equalInType-NAT→ i w1 (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa) w1 (⊑-refl· _)

    cak : Σ ℕ (λ k → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇛ NUM k at w1)
    cak = fst eqn , fst (snd eqn)

    m : ℕ
    m = fst cak

    ca : Σ 𝕎· (λ w' → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from w1 to w')
    ca = ⇛→⇓from-to (snd cak)

    e2 : w1 ⊑· fst ca
    e2 = ⇓from-to→⊑ {w1} {fst ca} (snd ca)

    cg : Σ ℕ (λ k → get0 name ⇓ NUM k from (fst ca) to (fst ca))
    cg = lower (∀𝕎-getT0-NUM→∀𝕎get0-NUM w1 name g0 (fst ca) e2)
-- TODO: add a 'fresh' to testM, and make it so that it adds an "entry" in the world
-- change choose so that the name is directly a parameter?




shiftNameDown-renn-shiftNameUp : (name : Name) (F f : Term)
                                 → # F
                                 → # f
                                 → shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) (shiftNameUp 0 f)))
                                    ≡ testM name F f
shiftNameDown-renn-shiftNameUp name F f cF cf
  rewrite shiftUp-shiftNameUp 0 0 F
        | shiftUp-shiftNameUp 0 0 f
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct f cf)
        | shiftUp-shiftNameUp 3 0 f
        | #shiftUp 3 (ct f cf)
        | renn-shiftNameUp 0 (suc name) F
        | renn-shiftNameUp 0 (suc name) f
        | shiftNameDownUp 0 F
        | shiftNameDownUp 0 f = refl



-- MOVE to newChoiceDef
¬newChoiceT∈dom𝕎 : (w : 𝕎·) (t : Term) → ¬ newChoiceT w t ∈ dom𝕎· w
¬newChoiceT∈dom𝕎 w t i = ¬fresh∈dom𝕎 w (↓vars (names t)) i


⇓APPLY-upd→⇓νtestM : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                      → ∈Type i w #BAIRE→NAT F
                      → ∈Type i w #BAIRE f
                      → Σ ℕ (λ k → νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ NUM k at w)
⇓APPLY-upd→⇓νtestM nc cn kb i w F f ∈F ∈f =
  fst z , step-⇓-trans s1 (snd z)
  where
    tM : Term
    tM = testM 0 (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : step (νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)) w ≡ just (testM name ⌜ F ⌝ ⌜ f ⌝ , w1)
    s1 = ≡just (≡pair (shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl)

    z : Σ ℕ (λ k → testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM k at w1)
    z = ⇓APPLY-upd→⇓testM nc cn kb i w1 name F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) comp1



#shiftNameUp : ℕ → CTerm → CTerm
#shiftNameUp n t = ct (shiftNameUp n ⌜ t ⌝) (→#shiftNameUp n {⌜ t ⌝} (CTerm.closed t))


differ⇓from-to : (gc0 : getT-chooseT) (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name)
                 (w1 w2 w1' : 𝕎·) (a b v : Term)
                 → isValue v
                 → compatible· name1 w1 Res⊤
                 → compatible· name2 w1' Res⊤
                 → ∀𝕎-get0-NUM w1 name1
                 → differ name1 name2 f a b
                 → getT 0 name1 w1 ≡ getT 0 name2 w1'
                 → a ⇓ v from w1 to w2
                 → Σ 𝕎· (λ w2' → Σ Term (λ v' →
                     b ⇓ v' from w1' to w2' × differ name1 name2 f v v' × getT 0 name1 w2 ≡ getT 0 name2 w2'))
differ⇓from-to gc0 f cf nnf name1 name2 w1 w2 w1' a b v isv compat1 compat2 gt0n diff eqget comp =
  differ⇓ gc0 f cf nnf name1 name2 (fst comp) w1 w2 w1' a b v isv compat1 compat2 gt0n diff eqget (snd comp)


differ-APPLY-upd : (name1 name2 : Name) (F f : Term)
                   → ¬Names F
                   → differ name1 name2 f (appUpd name1 F f) (appUpd name2 F f)
differ-APPLY-upd name1 name2 F f nnF =
  differ-APPLY _ _ _ _ (differ-refl name1 name2 f F nnF) differ-upd
{--  differ-LET
    _ _ _ _
    (differ-APPLY _ _ (upd name1 f) (upd name2 f) (differ-refl name1 name2 f F nnF) differ-upd)
    (differ-APPLY _ _ _ _ {!!} (differ-NUM 0))
--}



≡ᵣ→⇓from-to : {w1 w2 : 𝕎·} {a b c : Term}
              → b ≡ c
              → a ⇓ b from w1 to w2
              → a ⇓ c from w1 to w2
≡ᵣ→⇓from-to {w1} {w2} {a} {b} {c} e comp rewrite e = comp



¬Names→shiftNameUp≡ : (t : Term) (n : ℕ) → ¬names t ≡ true → shiftNameUp n t ≡ t
¬Names→shiftNameUp≡ (VAR x) n nnt = refl
¬Names→shiftNameUp≡ NAT n nnt = refl
¬Names→shiftNameUp≡ QNAT n nnt = refl
¬Names→shiftNameUp≡ (LT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (QLT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (NUM x) n nnt = refl
¬Names→shiftNameUp≡ (IFLT t t₁ t₂ t₃) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₃ n (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) = refl
¬Names→shiftNameUp≡ (PI t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (LAMBDA t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (APPLY t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (FIX t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (LET t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (SUM t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (PAIR t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (SPREAD t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (SET t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (TUNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (UNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (QTUNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (INL t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (INR t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (DECIDE t t₁ t₂) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nnt) = refl
¬Names→shiftNameUp≡ (EQ t t₁ t₂) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nnt) = refl
¬Names→shiftNameUp≡ AX n nnt = refl
¬Names→shiftNameUp≡ FREE n nnt = refl
¬Names→shiftNameUp≡ (CHOOSE t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (TSQUASH t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (TTRUNC t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (TCONST t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (SUBSING t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (DUM t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (FFDEFS t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (UNIV x) n nnt = refl
¬Names→shiftNameUp≡ (LIFT t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (LOWER t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (SHRINK t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl


νtestM-NAT-shift : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT) (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F -- We require F to be pure
             → #¬Names f -- We require f to be pure
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → NATeq w (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)) (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f))
νtestM-NAT-shift nc cn kb gc i w F f nnF nnf ∈F ∈f =
  k , ack , ack
  where
    tM : Term
    tM = testM 0 (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ testM name ⌜ F ⌝ ⌜ f ⌝ from w to w1
    s1 = 1 , ≡pair (shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

    w2 : 𝕎·
    w2 = chooseT name w1 (NUM 0)

    cs : set0 name ⇓ AX from w1 to w2
    cs = 1 , refl

    e2 : w1 ⊑· w2
    e2 = ⇓from-to→⊑ {w1} {w2} cs

    -- we prove that in w2 name's value is 0
    gc0 : getT 0 name w2 ≡ just (NUM 0)
    gc0 = gc w1 name 0 comp1

    g0 : ∀𝕎 w2 (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
    g0 = cn nc name w1 0 comp1

    eqa : ∈Type i w2 #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→
            (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) w2 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w2 name f g0 (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))

    eqn : NATeq w2 (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
    eqn = kb (equalInType-NAT→ i w2 (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa) w2 (⊑-refl· _)

    cak : Σ ℕ (λ k → appUpd name ⌜ F ⌝ ⌜ f ⌝ ⇛ NUM k at w2)
    cak = fst eqn , fst (snd eqn)

    m : ℕ
    m = fst cak

    ca : Σ 𝕎· (λ w' → appUpd name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM m from w2 to w')
    ca = ⇛→⇓from-to (snd cak)

    w3 : 𝕎·
    w3 = fst ca

    e3 : w2 ⊑· w3
    e3 = ⇓from-to→⊑ {w2} {w3} (snd ca)

    gt0 : Σ ℕ (λ k → getT 0 name w3 ≡ just (NUM k))
    gt0 = lower (g0 w3 e3)

    k : ℕ
    k = fst gt0

    gk : get0 name ⇓ NUM k from w3 to w3
    gk = 1 , step-APPLY-CS (NUM k) w3 0 name (snd gt0)

    pbk : probeM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM k from w2 to w3
    pbk = ⇓-trans₂ (SEQ⇓₁ (snd ca)) (⇓-trans₂ (SEQ-val⇓ w3 (NUM m) (get0 name) tt) gk)

    ack : νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇛ NUM k at w
    ack w' e' = lift (⇓-from-to→⇓ {w'} {w3'} {νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)} {NUM k}
                                   (⇓-trans₂ {w'} {w1'} {w3'} {νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)} {testM name' ⌜ F ⌝ ⌜ f ⌝} {NUM k}
                                             s1' (⇓-trans₂ {w1'} {w2'} {w3'} {testM name' ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name' ⌜ F ⌝ ⌜ f ⌝)} {NUM k}
                                                           (SEQ⇓₁ {w1'} {w2'} {set0 name'} {AX} {probeM name' ⌜ F ⌝ ⌜ f ⌝}  cs')
                                                           (⇓-trans₂ (SEQ-val⇓ w2' AX (probeM name' ⌜ F ⌝ ⌜ f ⌝) tt) pb'))))
      where
        name' : Name
        name' = newChoiceT w' tM

        w1' : 𝕎·
        w1' = startNewChoiceT Res⊤ w' tM

        e1' : w' ⊑· w1'
        e1' = startNewChoiceT⊏ Res⊤ w' tM

        comp1' : compatible· name' w1' Res⊤
        comp1' = startChoiceCompatible· Res⊤ w' name' (¬newChoiceT∈dom𝕎 w' tM)

        s1' : νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ testM name' ⌜ F ⌝ ⌜ f ⌝ from w' to w1'
        s1' = 1 , ≡pair (shiftNameDown-renn-shiftNameUp name' ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

        w2' : 𝕎·
        w2' = chooseT name' w1' (NUM 0)

        cs' : set0 name' ⇓ AX from w1' to w2'
        cs' = 1 , refl

        e2' : w1' ⊑· w2'
        e2' = ⇓from-to→⊑ {w1'} {w2'} cs'

        -- we prove that in w2 name's value is 0
        gc0' : getT 0 name' w2' ≡ just (NUM 0)
        gc0' = gc w1' name' 0 comp1'

        eqgt : getT 0 name w2 ≡ getT 0 name' w2'
        eqgt = trans gc0 (sym gc0')

        compat1 : compatible· name w2 Res⊤
        compat1 = ⊑-compatible· e2 comp1

        compat2 : compatible· name' w2' Res⊤
        compat2 = ⊑-compatible· e2' comp1'

        gt0n : ∀𝕎-get0-NUM w2 name
        gt0n w' e' = cn nc name w1 0 comp1 w' e'

        df : Σ 𝕎· (λ w3' → Σ Term (λ v' →
              appUpd name' ⌜ F ⌝ ⌜ f ⌝ ⇓ v' from w2' to w3' × differ name name' ⌜ f ⌝ (NUM m) v' × getT 0 name w3 ≡ getT 0 name' w3'))
        df = differ⇓from-to
               gc ⌜ f ⌝ (CTerm.closed f) nnf name name' w2 w3 w2'
               (appUpd name ⌜ F ⌝ ⌜ f ⌝)
               (appUpd name' ⌜ F ⌝ ⌜ f ⌝)
               (NUM m) tt compat1 compat2 gt0n
               (differ-APPLY-upd name name' ⌜ F ⌝ ⌜ f ⌝ nnF)
               eqgt (snd ca)

        w3' : 𝕎·
        w3' = fst df

        v' : Term
        v' = fst (snd df)

        dfv' : differ name name' ⌜ f ⌝ (NUM m) v'
        dfv' = fst (snd (snd (snd df)))

        df0 : appUpd name' ⌜ F ⌝ ⌜ f ⌝ ⇓ v' from w2' to w3'
        df0 = fst (snd (snd df))

        df1 : appUpd name' ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM m from w2' to w3'
        df1 = ≡ᵣ→⇓from-to (differ-NUM→ dfv') df0

        pb' : probeM name' ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM k from w2' to w3'
        pb' = ⇓-trans₂
                (SEQ⇓₁ df1)
                (⇓-trans₂
                  (SEQ-val⇓ w3' (NUM m) (get0 name') tt)
                  (1 , step-APPLY-CS (NUM k) w3' 0 name' (trans (sym (snd (snd (snd (snd df))))) (snd gt0))))



νtestM-NAT : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
             (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F -- We require F to be pure
             → #¬Names f -- We require f to be pure
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → NATeq w (#νtestM F f) (#νtestM F f)
νtestM-NAT nc cn kb gc i w F f nnF nnf ∈F ∈f = concl h
  where
    h : NATeq w (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)) (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f))
    h = νtestM-NAT-shift nc cn kb gc i w F f nnF nnf ∈F ∈f

    concl : NATeq w (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)) (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f))
            → NATeq w (#νtestM F f) (#νtestM F f)
    concl rewrite ¬Names→shiftNameUp≡ ⌜ F ⌝ 0 nnF | ¬Names→shiftNameUp≡ ⌜ f ⌝ 0 nnf = λ x → x



testM-NAT : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
            (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
            → #¬Names F
            → #¬Names f
            → ∈Type i w #BAIRE→NAT F
            → ∈Type i w #BAIRE f
            → ∈Type i w #NAT (#νtestM F f)
testM-NAT nc cn kb gc i w name F f nnF nnf ∈F ∈f =
  →equalInType-NAT i w (#νtestM F f) (#νtestM F f) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → NATeq w' (#νtestM F f) (#νtestM F f))
    aw w' e' = νtestM-NAT nc cn kb gc i w' F f nnF nnf (equalInType-mon ∈F w' e') (equalInType-mon ∈f w' e')


lam2AX : Term
lam2AX = LAMBDA (LAMBDA AX)


#contBody : (F f : CTerm) → CTerm
#contBody F f = ct (contBody ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # contBody ⌜ F ⌝ ⌜ f ⌝
    c rewrite CTerm.closed f
            | #shiftUp 0 f
            | #shiftUp 0 F
            | CTerm.closed F
            | CTerm.closed f = refl


#[0]BAIRE : CTerm0
#[0]BAIRE = ct0 BAIRE c
  where
    c : #[ [ 0 ] ] BAIRE
    c = refl



#[1]FUN : CTerm1 → CTerm1 → CTerm1
#[1]FUN a b = ct1 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[1]EQ : CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]EQ a b c = ct1 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ [ 1 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b))
                        (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ [ 1 ]} (CTerm1.closed c))))


--fvars-NATn : (n : Term) → fvars (NATn n) ≡ fvars n
--fvars-NATn n = ?


lowerVars-fvars-[0,1,2] : {l : List Var}
                        → l ⊆ (0 ∷ 1 ∷ [ 2 ])
                        → lowerVars l ⊆ 0 ∷ [ 1 ]
lowerVars-fvars-[0,1,2] {0 ∷ l} h x = lowerVars-fvars-[0,1,2] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ [ 2 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ [ 2 ]) →  x₁ ∈ 0 ∷ [ 1 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
lowerVars-fvars-[0,1,2] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2] (λ z → h (there z)) x


→fvars-shiftUp⊆-[0,1,2] : {t : Term}
                           → fvars t ⊆ 0 ∷ 1 ∷ []
                           → fvars (shiftUp 0 t) ⊆ 0 ∷ 1 ∷ [ 2 ]
→fvars-shiftUp⊆-[0,1,2] {t} h {x} i rewrite fvars-shiftUp≡ 0 t = z₃
  where
     y : Var
     y = fst (∈-map⁻ suc i)

     j : y ∈ fvars t
     j = fst (snd (∈-map⁻ suc i))

     e : x ≡ suc y
     e = snd (snd (∈-map⁻ suc i))

     z₁ : y ∈ 0 ∷ 1 ∷ []
     z₁ = h j

     z→ : y ∈ 0 ∷ 1 ∷ [] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ []
     z→ (here px) rewrite px = there (here refl)
     z→ (there (here px)) rewrite px = there (there (here refl))

     z₂ : suc y ∈ 0 ∷ 1 ∷ 2 ∷ []
     z₂ = z→ z₁

     z₃ : x ∈ 0 ∷ 1 ∷ 2 ∷ []
     z₃ rewrite e = z₂


→fvars-shiftUp⊆-[0,1] : {t : Term}
                           → fvars t ⊆ [ 0 ]
                           → fvars (shiftUp 0 t) ⊆ 0 ∷ [ 1 ]
→fvars-shiftUp⊆-[0,1] {t} h {x} i rewrite fvars-shiftUp≡ 0 t = z₃
  where
     y : Var
     y = fst (∈-map⁻ suc i)

     j : y ∈ fvars t
     j = fst (snd (∈-map⁻ suc i))

     e : x ≡ suc y
     e = snd (snd (∈-map⁻ suc i))

     z₁ : y ∈ [ 0 ]
     z₁ = h j

     z→ : y ∈ [ 0 ] → suc y ∈ 0 ∷ [ 1 ]
     z→ (here px) rewrite px = there (here refl)

     z₂ : suc y ∈ 0 ∷ [ 1 ]
     z₂ = z→ z₁

     z₃ : x ∈ 0 ∷ [ 1 ]
     z₃ rewrite e = z₂


#[1]BAIREn : CTerm1 → CTerm1
#[1]BAIREn n = ct1 (BAIREn ⌜ n ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] BAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (NATn ⌜ n ⌝) NAT | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝))) =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {0 ∷ [ 1 ]}
           (lowerVars-fvars-[0,1,2] {fvars (shiftUp 0 ⌜ n ⌝)} (→fvars-shiftUp⊆-[0,1,2] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {0 ∷ [ 1 ]} (CTerm1.closed n))))



#[0]BAIREn : CTerm0 → CTerm0
#[0]BAIREn n = ct0 (BAIREn ⌜ n ⌝) c
  where
    c : #[ [ 0 ] ] BAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (NATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | lowerVars-fvars-CTerm0≡[] n =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {[ 0 ]}
            (lowerVars-fvars-[0,1] {fvars (shiftUp 0 ⌜ n ⌝)}
                                   (→fvars-shiftUp⊆-[0,1] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {[ 0 ]} (CTerm0.closed n))))


#BAIREn : CTerm → CTerm
#BAIREn n = ct (BAIREn ⌜ n ⌝) c
  where
    c : # BAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (NATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n


#[1]NAT : CTerm1
#[1]NAT = ct1 NAT c
  where
    c : #[ 0 ∷ [ 1 ] ] NAT
    c = refl



#contBody≡ : (F f : CTerm)
            → #contBody F f
               ≡ #SUM #NAT
                      (#[0]PI #[0]BAIRE
                              (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                       (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))
#contBody≡ F f = CTerm≡ refl



#lam2AX : CTerm
#lam2AX = ct lam2AX refl



sub0-contBodyPI : (F f a : CTerm)
                  → sub0 a (#[0]PI #[0]BAIRE
                                    (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                             (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))
                    ≡ #PI #BAIRE
                          (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ a ⌟))
                                   (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))
sub0-contBodyPI F f a
  rewrite CTerm→CTerm1→Term f
  = CTerm≡ (≡PI refl (≡PI e1 e2))
  where
    e1 : EQ (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ⌜ f ⌝))
            (VAR 0)
            (PI (SET NAT (LT (VAR 0) (shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))))) NAT)
         ≡ EQ ⌜ f ⌝ (VAR 0) (PI (SET NAT (LT (VAR 0) (shiftUp 0 ⌜ a ⌝))) NAT)
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a
             | #subv 1 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 2 a | #shiftDown 2 f | #shiftDown 1 f = refl

    e2 : EQ (APPLY (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) (shiftUp 0 ⌜ F ⌝)))
                   (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) (shiftUp 0 ⌜ f ⌝))))
            (APPLY (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) (shiftUp 0 ⌜ F ⌝)))
                   (VAR 1))
            NAT
         ≡ EQ (APPLY (shiftUp 0 ⌜ F ⌝) (shiftUp 0 ⌜ f ⌝)) (APPLY (shiftUp 0 ⌜ F ⌝) (VAR 1)) NAT
    e2 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 F | #shiftUp 0 f
             | #subv 2 ⌜ a ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #subv 2 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 2 F | #shiftDown 2 f = refl


sub0-contBodyPI-PI : (F f a g : CTerm)
                    → sub0 g (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ a ⌟))
                                       (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))
                       ≡ #FUN (#EQ f g (#BAIREn a)) (#EQ (#APPLY F f) (#APPLY F g) #NAT)
sub0-contBodyPI-PI F f a g
  rewrite CTerm→CTerm1→Term f =
  CTerm≡ (≡PI e1 e2)
  where
    e1 : EQ (shiftDown 0 (subv 0 (shiftUp 0 ⌜ g ⌝) ⌜ f ⌝))
            (shiftDown 0 (shiftUp 0 ⌜ g ⌝))
            (PI (SET NAT (LT (VAR 0) (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)) (shiftUp 0 ⌜ a ⌝))))) NAT)
         ≡ EQ ⌜ f ⌝ ⌜ g ⌝ (PI (SET NAT (LT (VAR 0) (shiftUp 0 ⌜ a ⌝))) NAT)
    e1 rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 a
             | #subv 0 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #subv 1 ⌜ g ⌝ ⌜ a ⌝ (CTerm.closed a)
             | #shiftDown 0 f | #shiftDown 1 a | #shiftDown 0 g = refl

    e2 : EQ (APPLY (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)) (shiftUp 0 ⌜ F ⌝)))
                   (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))))
            (APPLY (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)) (shiftUp 0 ⌜ F ⌝)))
                   (shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))))
            NAT
         ≡ EQ (APPLY (shiftUp 0 ⌜ F ⌝) (shiftUp 0 ⌜ f ⌝)) (APPLY (shiftUp 0 ⌜ F ⌝) (shiftUp 0 ⌜ g ⌝)) NAT
    e2 rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 F | #shiftUp 0 f
             | #subv 1 ⌜ g ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #subv 1 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 1 F | #shiftDown 1 f | #shiftDown 1 g = refl



#NATn : CTerm → CTerm
#NATn n = ct (NATn ⌜ n ⌝) c
  where
    c : # NATn ⌜ n ⌝
    c rewrite ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n



≡BAIREn : (n : CTerm) → #BAIREn n ≡ #FUN (#NATn n) #NAT
≡BAIREn n = CTerm≡ refl


-- MOVE to terms
#[0]LT : CTerm0 → CTerm0 → CTerm0
#[0]LT a b = ct0 (LT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LT ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))


≡NATn : (n : CTerm) → #NATn n ≡ #SET #NAT (#[0]LT #[0]VAR ⌞ n ⌟)
≡NATn n rewrite CTerm→CTerm0→Term n = CTerm≡ (≡SET refl e)
  where
    e : LT (VAR 0) (shiftUp 0 ⌜ n ⌝) ≡ LT (VAR 0) ⌜ n ⌝
    e rewrite #shiftUp 0 n = refl



sub0-NATn-body : (a n : CTerm) → sub0 a (#[0]LT #[0]VAR ⌞ n ⌟) ≡ #LT a n
sub0-NATn-body a n rewrite CTerm→CTerm0→Term n = CTerm≡ e
  where
    e : LT (shiftDown 0 (shiftUp 0 ⌜ a ⌝)) (shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ n ⌝))
        ≡ LT (CTerm.cTerm a) ⌜ n ⌝
    e rewrite #shiftUp 0 a
            | #subv 0 ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 n | #shiftDown 0 a = refl


→equalTypesLT : {i : ℕ} {w : 𝕎·} {a₁ a₂ b₁ b₂ : CTerm}
                 → equalInType i w #NAT a₁ a₂
                 → equalInType i w #NAT b₁ b₂
                 → equalTypes i w (#LT a₁ b₁) (#LT a₂ b₂)
→equalTypesLT {i} {w} {a₁} {a₂} {b₁} {b₂} ea eb =
  eqTypes-local (∀𝕎-□Func2 aw ea1 eb1)
  where
    ea1 : □· w (λ w' _ → NATeq w' a₁ a₂)
    ea1 = equalInType-NAT→ i w a₁ a₂ ea

    eb1 : □· w (λ w' _ → NATeq w' b₁ b₂)
    eb1 = equalInType-NAT→ i w b₁ b₂ eb

    aw : ∀𝕎 w (λ w' e' → NATeq w' a₁ a₂ → NATeq w' b₁ b₂ → equalTypes i w' (#LT a₁ b₁) (#LT a₂ b₂))
    aw  w1 e1 ha hb =
      EQTLT a₁ a₂ b₁ b₂ (#compAllRefl (#LT a₁ b₁) w1) (#compAllRefl (#LT a₂ b₂) w1) ha hb


→equalTypesNATn : (i : ℕ) (w : 𝕎·) (a₁ a₂ : CTerm)
                   → equalInType i w #NAT a₁ a₂
                   → equalTypes i w (#NATn a₁) (#NATn a₂)
→equalTypesNATn i w a₁ a₂ ea =
  ≡CTerm→eqTypes
    (sym (≡NATn a₁))
    (sym (≡NATn a₂))
    (eqTypesSET← (λ w' e' → eqTypesNAT) aw1)
  where
    aw2 : ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' #NAT b₁ b₂
                       → equalTypes i w' (#LT b₁ a₁) (#LT b₂ a₂))
    aw2 w1 e1 b₁ b₂ eb = →equalTypesLT eb (equalInType-mon ea w1 e1)

    aw1 : ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' #NAT b₁ b₂
                       → equalTypes i w' (sub0 b₁ (#[0]LT #[0]VAR ⌞ a₁ ⌟)) (sub0 b₂ (#[0]LT #[0]VAR ⌞ a₂ ⌟)))
    aw1 w1 e1 b₁ b₂ eb = ≡CTerm→eqTypes (sym (sub0-NATn-body b₁ a₁)) (sym (sub0-NATn-body b₂ a₂)) (aw2 w1 e1 b₁ b₂ eb)



→equalTypesBAIREn : (i : ℕ) (w : 𝕎·) (a₁ a₂ : CTerm)
                     → equalInType i w #NAT a₁ a₂
                     → equalTypes i w (#BAIREn a₁) (#BAIREn a₂)
→equalTypesBAIREn i w a₁ a₂ ea =
  ≡CTerm→eqTypes
    (sym (≡BAIREn a₁))
    (sym (≡BAIREn a₂))
    (eqTypesFUN← (→equalTypesNATn i w a₁ a₂ ea) eqTypesNAT)




∈NATn→∈NAT : {i : ℕ} {w : 𝕎·} {a b n : CTerm}
              → equalInType i w #NAT n n
              → equalInType i w (#NATn n) a b
              → equalInType i w #NAT a b
∈NATn→∈NAT {i} {w} {a} {b} {n} en ea =
  →equalInType-NAT i w a b (Mod.□-idem M (Mod.∀𝕎-□Func M aw1 eb2))
  where
    eb1 : equalInType i w (#SET #NAT (#[0]LT #[0]VAR ⌞ n ⌟)) a b
    eb1 = ≡CTerm→equalInType (≡NATn n) ea

    eb2 : □· w (λ w' _ → SETeq (equalInType i w' #NAT) (λ x y ea → equalInType i w' (sub0 x (#[0]LT #[0]VAR ⌞ n ⌟))) a b)
    eb2 = equalInType-SET→ eb1

    aw1 : ∀𝕎 w (λ w' e' → SETeq (equalInType i w' #NAT) (λ x y ea₁ → equalInType i w' (sub0 x (#[0]LT #[0]VAR (CTerm→CTerm0 n)))) a b
                        → □· w' (↑wPred' (λ w'' _ → NATeq w'' a b) e'))
    aw1 w1 e1 (x , ex , ey) = Mod.∀𝕎-□Func M (λ w2 e2 s z → s) (equalInType-NAT→ i w1 a b ex)


∈BAIRE→∈BAIREn : {i : ℕ} {w : 𝕎·} {f g n : CTerm}
                  → equalInType i w #NAT n n
                  → equalInType i w #BAIRE f g
                  → equalInType i w (#BAIREn n) f g
∈BAIRE→∈BAIREn {i} {w} {f} {g} {n} en ef =
  ≡CTerm→equalInType
    (sym (≡BAIREn n))
    (equalInType-FUN (λ w1 e1 → →equalTypesNATn i w1 n n (equalInType-mon en w1 e1))
                     (λ w1 e1 → eqTypesNAT)
                     aw)
  where
    ef1 : equalInType i w (#FUN #NAT #NAT) f g
    ef1 = ≡CTerm→equalInType #BAIRE≡ ef

    ef2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂ → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    ef2 = equalInType-FUN→ ef1

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn n) a₁ a₂
                      → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    aw w1 e1 a₁ a₂ ea = ef2 w1 e1 a₁ a₂ (∈NATn→∈NAT (equalInType-mon en w1 e1) ea)



∈BAIRE→NAT→ : {i : ℕ} {w : 𝕎·} {F f g : CTerm}
                → ∈Type i w #BAIRE→NAT F
                → equalInType i w #BAIRE f g
                → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
∈BAIRE→NAT→ {i} {w} {F} {f} {g} ∈F ∈f =
  equalInType-FUN→
    {i} {w} {#BAIRE} {#NAT} {F} {F} ∈F w (⊑-refl· _) f g
    ∈f



equalTypes-contBodyPI : (i : ℕ) (w : 𝕎·) (F f : CTerm)
                        → ∈Type i w #BAIRE→NAT F
                        → ∈Type i w #BAIRE f
                        → ∀𝕎 w (λ w' e →
                             (a₁ a₂ : CTerm)
                             → equalInType i w' #NAT a₁ a₂
                             → equalTypes i w'
                                 (sub0 a₁ (#[0]PI #[0]BAIRE
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
                                 (sub0 a₂ (#[0]PI #[0]BAIRE
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
equalTypes-contBodyPI i w F f ∈F ∈f w1 e1 a₁ a₂ ea =
  ≡CTerm→eqTypes (sym (sub0-contBodyPI F f a₁)) (sym (sub0-contBodyPI F f a₂)) ea1
  where
    ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                         → equalTypes i w2
                               (#FUN (#EQ f g₁ (#BAIREn a₁)) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                               (#FUN (#EQ f g₂ (#BAIREn a₂)) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT)))
    ea2 w2 e2 g₁ g₂ eg =
      eqTypesFUN←
        (eqTypesEQ← (→equalTypesBAIREn i w2 a₁ a₂ (equalInType-mon ea w2 e2))
                     (∈BAIRE→∈BAIREn (equalInType-refl (equalInType-mon ea w2 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                     (∈BAIRE→∈BAIREn (equalInType-refl (equalInType-mon ea w2 e2)) eg))
        (eqTypesEQ← eqTypesNAT
                    (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                    (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg))

    ea1 : equalTypes i w1
            (#PI #BAIRE
                 (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ a₁ ⌟))
                          (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
            (#PI #BAIRE
                 (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ a₂ ⌟))
                          (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
    ea1 = eqTypesPI← (λ w' _ → eqTypesBAIRE)
                      (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contBodyPI-PI F f a₁ g₁)) (sym (sub0-contBodyPI-PI F f a₂ g₂)) (ea2 w2 e2 g₁ g₂ eg))


continuity : (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → ∈Type i w (#contBody F f) (#PAIR (#νtestM F f) #lam2AX)
continuity i w F f ∈F ∈f =
  ≡CTerm→equalInType
    (sym (#contBody≡ F f))
    h0
  where
    h0 : ∈Type i w (#SUM #NAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                          (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
                   (#PAIR (#νtestM F f) #lam2AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesNAT) (equalTypes-contBodyPI i w F f ∈F ∈f) {!!}

\end{code}
