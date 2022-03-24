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


probe : (name : Name) (F : Term) (n : Term) (f : Term) → Term
probe name F n f = LET (APPLY F (bound name n f))
                       (IFC0 (APPLY (CS name) (NUM 0)) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains ℂ₀


oldtest : (name : Name) (F : Term) (n : Term) (f : Term) → Term
oldtest name F n f = LET (APPLY F (bound name n f))
                         (LET (IFC0 (APPLY (CS name) (NUM 0)) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains ℂ₀
                              (SEQ (set name) -- resets the reference to ℂ₀
                                   (VAR 0)))


test : (name : Name) (F : Term) (n : Term) (f : Term) → Term
test name F n f = SEQ (set name) (probe name F n f)


setT : (name : Name) (T : Term) → Term
setT name t = CHOOSE (NAME name) t


set0 : (name : Name) → Term
set0 name = setT name (NUM 0)


get0 : (name : Name) → Term
get0 name = APPLY (CS name) (NUM 0)


updGt : (name : Name) (t : Term) → Term
updGt name t = IFLT (get0 name) t (setT name t) AX


-- TODO: we need choose to update the world only if the number is higher than the one stored
-- This will be specified as a constraint of the 'choose' operator from getChoice.lagda
-- We throw in a CBV to reduce the argument to a number
upd : (name : Name) (f : Term) → Term
upd name f = LAMBDA (LET (VAR 0) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))))


probeM : (name : Name) (F f : Term) → Term
probeM name F f = SEQ (APPLY F (upd name f)) (get0 name)


testM : (name : Name) (F f : Term) → Term
testM name F f = SEQ (set0 name) (probeM name F f)


νtestM : (F f : Term) → Term
νtestM F f = FRESH (testM 0 F f)


NATn : Term → Term
NATn n = SET NAT (LT (VAR 0) n)


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


→≡pair : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
→≡pair e f rewrite e | f = refl


→≡LET : {a₁ a₂ b₁ b₂ : Term} → a₁ ≡ a₂ → b₁ ≡ b₂ → LET a₁ b₁ ≡ LET a₂ b₂
→≡LET e f rewrite e | f = refl


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


sub-APPLY : (a b c : Term) → sub a (APPLY b c) ≡ APPLY (sub a b) (sub a c)
sub-APPLY a b c = refl


→sub-APPLY : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (APPLY b c) ≡ APPLY b' c'
→sub-APPLY {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-APPLY a b c


sub-VAR0 : (a : Term) → sub a (VAR 0) ≡ a
sub-VAR0 a rewrite shiftDownUp a 0 = refl


sub-IFC0 : (a b c d : Term)
           → sub a (IFC0 b c d) ≡ IFC0 (sub a b) (sub a c) (sub a d)
sub-IFC0 a b c d = refl


→sub-IFC0 : {a b c d b' c' d' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a (IFC0 b c d) ≡ IFC0 b' c' d'
→sub-IFC0 {a} {b} {c} {d} {b'} {c'} {d'} eb ec ed
  rewrite sym eb | sym ec | sym ed =
  refl


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
                     → sub (NUM m) (IFC0 (APPLY (CS name) (NUM 0)) (INL (VAR 0)) (INR AX))
                        ≡ IFC0 (APPLY (CS name) (NUM 0)) (INL (NUM m)) (INR AX)
sub-num-probe-body {m} {name} = refl


≡ₗ→⇓from-to : {a b c : Term} {w1 w2 : 𝕎·}
              → c ≡ a
              → c ⇓ b from w1 to w2
              → a ⇓ b from w1 to w2
≡ₗ→⇓from-to {a} {b} {c} {w1} {w2} e comp rewrite e = comp



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


getChoice→getT : {n : ℕ} {name : Name} {w : 𝕎·} {c : ℂ·}
                  → getChoice· n name w ≡ just c
                  → getT n name w ≡ just ⌜ ℂ→C· c ⌝
getChoice→getT {n} {name} {w} {c} getc rewrite getc = refl



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


≡ℂ→≡ℂ→C : {a b : ℂ·}
             → a ≡ b
             → ℂ→C· a ≡ ℂ→C· b
≡ℂ→≡ℂ→C {a} {b} e rewrite e = refl


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

-- Prove this for the current world, and show that if F and f cannot read then this is true for all extensions too

-- Do we need to constrain F's type to be in (BAIRE→NAT!)? -- No, doesn't make sense: what function is going to inhabit that type?

-- Check what world (#APPLY F (#bound name n f)) ends up in and name's value in that world
-- and compare it with with ℂ₀ before instantiating the conclusion
-- Because we used NAT, this requires choices to be numbers (should be QTNAT in the union)



sub-LET : (a b c : Term) → # a → sub a (LET b c) ≡ LET (sub a b) (shiftDown 1 (subv 1 a c))
sub-LET a b c ca
  rewrite #shiftUp 0 (ct a ca)
        | #shiftUp 0 (ct a ca)
  = →≡LET refl refl


→sub-LET : {a b c b' c' : Term} → # a
            → sub a b ≡ b'
            → shiftDown 1 (subv 1 a c) ≡ c'
            → sub a (LET b c) ≡ LET b' c'
→sub-LET {a} {b} {c} {b'} {c'} ca eb ec rewrite sym eb | sym ec = sub-LET a b c ca


CTerm→CTerm0→Term : (a : CTerm) → ⌜ CTerm→CTerm0 a ⌝ ≡ ⌜ a ⌝
CTerm→CTerm0→Term (ct a c) = refl


CTerm→CTerm1→Term : (a : CTerm) → ⌜ CTerm→CTerm1 a ⌝ ≡ ⌜ a ⌝
CTerm→CTerm1→Term (ct a c) = refl



#subv : (n : ℕ) (t u : Term) → # u → subv n t u ≡ u
#subv n t u d rewrite subvNotIn n t u (#→¬∈ {u} d n) = refl



#⇛!-#APPLY-#UPD : (w : 𝕎·) (name : Name) (f : CTerm) (a : CTerm)
                   → #APPLY (#UPD name f) a #⇛! #LET a (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY ⌞ f ⌟ #[0]VAR)) at w
#⇛!-#APPLY-#UPD w name f a w1 e1
  = lift (1 , →≡pair (→sub-LET {⌜ a ⌝} {⌜ #[0]VAR ⌝} {⌜ #[1]SEQ (#[1]updGt name #[1]VAR0) (#[1]APPLY ⌞ f ⌟ #[1]VAR0) ⌝}
                                 (CTerm.closed a)
                                 (sub-VAR0 ⌜ a ⌝)
                                 (→≡LET refl
                                         (→≡APPLY e refl)))
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


-- MOVE to calculus
#¬read : CTerm → Bool
#¬read t = ¬read ⌜ t ⌝


-- MOVE to calculus
¬Read : Term → Set
¬Read t = ¬read t ≡ true


-- MOVE to calculus
#¬Read : CTerm → Set
#¬Read t = #¬read t ≡ true


-- MOVE to calculus
#names : CTerm → List Name
#names t = names ⌜ t ⌝


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



-- TODO: now we ned to prove that testM computes to the same number in all extensions of w
-- (as long as name does not occur in F or f)
⇓APPLY-upd→⇓testM : (w : 𝕎·) (name : Name) (F f : Term) (m : ℕ)
                    → # F
                    → # f
                    → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
                    → APPLY F (upd name f) ⇛ NUM m at w
                    → Σ ℕ (λ k → testM name F f ⇓ NUM k at w)
⇓APPLY-upd→⇓testM w name F f m cF cf {--nrF nrf gcn--} g0 ap =
  fst cg , ⇓-from-to→⇓ {w} {fst ca} {testM name F f} {NUM (fst cg)}
                       (⇓-trans₂ {w} {chooseT name w (NUM 0)} {fst ca} {testM name F f} {SEQ AX (probeM name F f)} {NUM (fst cg)}
                                 (SEQ⇓₁ {w} {chooseT name w (NUM 0)} {set0 name} {AX} {probeM name F f} cs)
                                 (⇓-trans₂ {chooseT name w (NUM 0)} {chooseT name w (NUM 0)} {fst ca} {SEQ AX (probeM name F f)} {probeM name F f} {NUM (fst cg)}
                                           (SEQ-AX⇓₁from-to (CTerm.closed (#probeM name (ct F cF) (ct f cf))))
                                           (⇓-trans₂ {chooseT name w (NUM 0)} {fst ca} {fst ca} {probeM name F f} {SEQ (NUM m) (get0 name)} {NUM (fst cg)}
                                                     (SEQ⇓₁ (snd ca))
                                                     (⇓-trans₂ {proj₁ ca} {proj₁ ca} {proj₁ ca} {SEQ (NUM m) (get0 name)} {get0 name} {NUM (proj₁ cg)}
                                                               (SEQ-val⇓₁from-to refl tt)
                                                               (snd cg)))))
  where
    cs : set0 name ⇓ AX from w to chooseT name w (NUM 0)
    cs = 1 , refl

    cs⊑ : w ⊑· chooseT name w (NUM 0)
    cs⊑ = ⇓from-to→⊑ {w} {chooseT name w (NUM 0)} cs

    ca : Σ 𝕎· (λ w' → APPLY F (upd name f) ⇓ NUM m from (chooseT name w (NUM 0)) to w')
    ca = ⇛→⇓from-to (∀𝕎-mon cs⊑ ap)

    ca⊑ : w ⊑· fst ca
    ca⊑ = ⊑-trans· cs⊑ (⇓from-to→⊑ {chooseT name w (NUM 0)} {fst ca} (snd ca))

    cg : Σ ℕ (λ k → get0 name ⇓ NUM k from (fst ca) to (fst ca))
    cg = lower (∀𝕎-getT0-NUM→∀𝕎get0-NUM w name g0 (fst ca) ca⊑)
-- TODO: add a 'fresh' to testM, and make it so that it adds an "entry" in the world
-- change choose so that the name is directly a parameter?



shiftUp-shiftNameUp : (c d : ℕ) (t : Term)
                      → shiftUp c (shiftNameUp d t) ≡ shiftNameUp d (shiftUp c t)
shiftUp-shiftNameUp c d (VAR x) = refl
shiftUp-shiftNameUp c d NAT = refl
shiftUp-shiftNameUp c d QNAT = refl
shiftUp-shiftNameUp c d (LT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (QLT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (NUM x) = refl
shiftUp-shiftNameUp c d (IFLT t t₁ t₂ t₃) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ | shiftUp-shiftNameUp c d t₃ = refl
shiftUp-shiftNameUp c d (PI t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (LAMBDA t) rewrite shiftUp-shiftNameUp (suc c) d t = refl
shiftUp-shiftNameUp c d (APPLY t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (FIX t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (LET t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (SUM t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (PAIR t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (SPREAD t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc (suc c)) d t₁ = refl
shiftUp-shiftNameUp c d (SET t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (TUNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (UNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (QTUNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (INL t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (INR t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (DECIDE t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ | shiftUp-shiftNameUp (suc c) d t₂ = refl
shiftUp-shiftNameUp c d (EQ t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ = refl
shiftUp-shiftNameUp c d AX = refl
shiftUp-shiftNameUp c d FREE = refl
shiftUp-shiftNameUp c d (CS x) = refl
shiftUp-shiftNameUp c d (NAME x) = refl
shiftUp-shiftNameUp c d (FRESH t) rewrite shiftUp-shiftNameUp c (suc d) t = refl
shiftUp-shiftNameUp c d (CHOOSE t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (IFC0 t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ = refl
shiftUp-shiftNameUp c d (TSQUASH t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (TTRUNC t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (TCONST t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (SUBSING t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (DUM t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (FFDEFS t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (UNIV x) = refl
shiftUp-shiftNameUp c d (LIFT t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (LOWER t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (SHRINK t) rewrite  shiftUp-shiftNameUp c d t = refl


renn-shiftNameUp : (n1 n2 : Name) (t : Term)
                   → renn n1 n2 (shiftNameUp n1 t) ≡ shiftNameUp n1 t
renn-shiftNameUp n1 n2 (VAR x) = refl
renn-shiftNameUp n1 n2 NAT = refl
renn-shiftNameUp n1 n2 QNAT = refl
renn-shiftNameUp n1 n2 (LT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (QLT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (NUM x) = refl
renn-shiftNameUp n1 n2 (IFLT t t₁ t₂ t₃) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ | renn-shiftNameUp n1 n2 t₃ = refl
renn-shiftNameUp n1 n2 (PI t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (LAMBDA t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (APPLY t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (FIX t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (LET t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (SUM t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (PAIR t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (SPREAD t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (SET t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (TUNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (UNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (QTUNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (INL t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (INR t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (DECIDE t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
renn-shiftNameUp n1 n2 (EQ t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
renn-shiftNameUp n1 n2 AX = refl
renn-shiftNameUp n1 n2 FREE = refl
renn-shiftNameUp n1 n2 (CS x) with x <? n1
... | yes p with x ≟ n1
... |    yes q rewrite q = ⊥-elim (1+n≰n p)
... |    no q = refl
renn-shiftNameUp n1 n2 (CS x) | no p with suc x ≟ n1
... |    yes q rewrite q = ⊥-elim (p ≤-refl)
... |    no q = refl
renn-shiftNameUp n1 n2 (NAME x) with x <? n1
... | yes p with x ≟ n1
... |    yes q rewrite q = ⊥-elim (1+n≰n p)
... |    no q = refl
renn-shiftNameUp n1 n2 (NAME x) | no p with suc x ≟ n1
... |    yes q rewrite q = ⊥-elim (p ≤-refl)
... |    no q = refl
renn-shiftNameUp n1 n2 (FRESH t) rewrite renn-shiftNameUp (suc n1) (suc n2) t = refl
renn-shiftNameUp n1 n2 (CHOOSE t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (IFC0 t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
renn-shiftNameUp n1 n2 (TSQUASH t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (TTRUNC t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (TCONST t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (SUBSING t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (DUM t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (FFDEFS t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (UNIV x) = refl
renn-shiftNameUp n1 n2 (LIFT t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (LOWER t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (SHRINK t) rewrite renn-shiftNameUp n1 n2 t = refl


predIf≤-sucIf≤ : (n : ℕ) (x : Name) → predIf≤ n (sucIf≤ n x) ≡ x
predIf≤-sucIf≤ n 0 with 0 <? n
... | yes p = refl
... | no p with 1 ≤? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl
predIf≤-sucIf≤ n (suc x) with suc x <? n
... | yes p with suc x ≤? n
... |    yes q = refl
... |    no q = ⊥-elim (q (≤-trans (_≤_.s≤s (<⇒≤ (n<1+n x))) p))
predIf≤-sucIf≤ n (suc x) | no p with suc (suc x) ≤? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl


shiftNameDownUp : (n : ℕ) (t : Term) → shiftNameDown n (shiftNameUp n t) ≡ t
shiftNameDownUp n (VAR x) = refl
shiftNameDownUp n NAT = refl
shiftNameDownUp n QNAT = refl
shiftNameDownUp n (LT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (QLT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (NUM x) = refl
shiftNameDownUp n (IFLT t t₁ t₂ t₃) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ | shiftNameDownUp n t₃ = refl
shiftNameDownUp n (PI t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (LAMBDA t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (APPLY t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (FIX t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (LET t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (SUM t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (PAIR t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (SPREAD t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (SET t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (TUNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (UNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (QTUNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (INL t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (INR t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (DECIDE t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
shiftNameDownUp n (EQ t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
shiftNameDownUp n AX = refl
shiftNameDownUp n FREE = refl
shiftNameDownUp n (CS x) rewrite predIf≤-sucIf≤ n x = refl
shiftNameDownUp n (NAME x) rewrite predIf≤-sucIf≤ n x = refl
shiftNameDownUp n (FRESH t) rewrite shiftNameDownUp (suc n) t = refl
shiftNameDownUp n (CHOOSE t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (IFC0 t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
shiftNameDownUp n (TSQUASH t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (TTRUNC t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (TCONST t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (SUBSING t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (DUM t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (FFDEFS t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (UNIV x) = refl
shiftNameDownUp n (LIFT t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (LOWER t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (SHRINK t) rewrite shiftNameDownUp n t = refl


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


≡just : {l : Level} {A : Set l} {a b : A} → a ≡ b → just a ≡ just b
≡just {l} {A} {a} {b} e rewrite e = refl


≡pair : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
≡pair {l} {k} {A} {B} {a₁} {a₂} {b₁} {b₂} e f rewrite e | f = refl


⇓APPLY-upd→⇓νtestM : (w : 𝕎·) (F f : Term) (m : ℕ)
                      → # F
                      → # f
--                      → ¬ 0 ∈ names F
--                      → ¬ 0 ∈ names f
--                    → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
--                    → APPLY F (upd name f) ⇛ NUM m at w
                    → Σ ℕ (λ k → νtestM (shiftNameUp 0 F) (shiftNameUp 0 f) ⇓ NUM k at w)
⇓APPLY-upd→⇓νtestM w F f m cF cf {--g0 ap--} {--n0F n0f--} =
  {!!}
-- use s2 and ⇓APPLY-upd→⇓testM
  where
    tM : Term
    tM = testM 0 (shiftNameUp 0 F) (shiftNameUp 0 f)

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    s1 : step (νtestM (shiftNameUp 0 F) (shiftNameUp 0 f)) w
         ≡ just (shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) (shiftNameUp 0 f))) , w1)
    s1 = ≡just refl

    s2 : step (νtestM (shiftNameUp 0 F) (shiftNameUp 0 f)) w
         ≡ just (testM name F f , w1)
    s2 rewrite s1 = ≡just (≡pair (shiftNameDown-renn-shiftNameUp name F f cF cf) refl)


testM-NAT : (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
            → #¬Read F
            → #¬Read f
            → ¬ name ∈ #names F
            → ¬ name ∈ #names f
            → ∈Type i w #BAIRE→NAT F
            → ∈Type i w #BAIRE f
            → ∈Type i w #NAT (#testM name F f)
testM-NAT i w name F f nrF nrf nnF nnf ∈F ∈f =
  ≡CTerm→∈Type
    (sym (#testM≡ name F f))
    (→equalInType-NAT
      i w
      (#SEQ (#set0 name) (#probeM name F f))
      (#SEQ (#set0 name) (#probeM name F f))
      (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa)))
  where
    aw : ∀𝕎 w (λ w' e' → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
                       → NATeq w' (#SEQ (#set0 name) (#probeM name F f)) (#SEQ (#set0 name) (#probeM name F f)))
    aw w1 e1 (m , c₁ , c₂) = {!!}

    eqa : ∈Type i w #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→ ∈F w (⊑-refl· _) (#upd name f) (#upd name f) (upd∈ i w name f {!!} ∈f)


\end{code}
