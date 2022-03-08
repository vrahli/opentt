\begin{code}
{-# OPTIONS --rewriting #-}

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
open import choiceExt
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
open import choiceBar


module continuity {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                  (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                  (X : ChoiceExt W C K G) (N : NewChoice {L} W C K G)
                  (F : Freeze {L} W C K P G N)
                  (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                  (CB : ChoiceBar W M C K P G X N F E) -- TODO - We won't need everything from there: use a different module
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)

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

open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)


-- turns 'f' into λy.(if n ≤ y then name:=ℂ₁);f(y)
-- ℂ₀ is treated as true here (i.e., "didn't reach n"), and ℂ₁ as false (i.e., "reached at least n")
bound : (name : Name) (n : Term) (f : Term) → Term
bound name n f = LAMBDA (SEQ (IFLE n (VAR 0) (CHOOSE (CS name) (ℂ→T ℂ₁·)) AX) (APPLY f (VAR 0)))


-- TODO: the name should be a fresh name, that does not occur in F
-- TODO: need union types?

-- We assume that initially name contains ℂ₀
test : (name : Name) (F : Term) (n : Term) (f : Term) → Term
test name F n f = LET (APPLY F (bound name n f))
                      (LET (IFC0 (APPLY (CS name) (NUM 0)) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains ℂ₀
                           (SEQ (CHOOSE (CS name) (ℂ→T ℂ₀·)) -- resets the reference to ℂ₀
                                (VAR 0)))


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


#test : (name : Name) (F : CTerm) (n : CTerm) (f : CTerm) → CTerm
#test name F n f = ct (test name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝) c
  where
    c : # test name ⌜ F ⌝ ⌜ n ⌝ ⌜ f ⌝
    c rewrite CTerm.closed (#bound name n f)
            | lowerVarsApp (fvars ⌜ ℂ→C· ℂ₀· ⌝) [ 0 ]
            | lowerVars-fvars-CTerm≡[] (ℂ→C· ℂ₀·)
            | CTerm.closed F = refl



#[0]AX : CTerm0
#[0]AX = ct0 AX refl


#BOUND : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#BOUND name n f =
  #LAMBDA (#[0]SEQ (#[0]IFLE ⌞ n ⌟ #[0]VAR (#[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟) #[0]AX)
                   (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#bound≡ : (name : Name) (n : CTerm) (f : CTerm) → #bound name n f ≡ #BOUND name n f
#bound≡ name n f = CTerm≡ refl


→≡pair : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
→≡pair e f rewrite e | f = refl


→≡LET : {a₁ a₂ b₁ b₂ : Term} → a₁ ≡ a₂ → b₁ ≡ b₂ → LET a₁ b₁ ≡ LET a₂ b₂
→≡LET e f rewrite e | f = refl


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


#⇛!-#APPLY-#BOUND : (w : 𝕎·) (name : Name) (n : CTerm) (f : CTerm) (a : CTerm)
                     → #APPLY (#BOUND name n f) a #⇛! #SEQ (#IFLE n a (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a) at w
#⇛!-#APPLY-#BOUND w name n f a w1 e1
  = lift (1 , →≡pair (→sub-SEQ {⌜ a ⌝}
                                 {⌜ #[0]IFLE ⌞ n ⌟ #[0]VAR (#[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟) #[0]AX ⌝}
                                 {⌜ #[0]APPLY ⌞ f ⌟ #[0]VAR ⌝}
                                 {⌜ #IFLE n a (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) #AX ⌝}
                                 {⌜ #APPLY f a ⌝}
                                 (CTerm.closed a) (CTerm0.closed (#[0]APPLY ⌞ f ⌟ #[0]VAR))
                                 (→sub-IFLE {⌜ a ⌝} {⌜ n ⌝} {⌜ #[0]VAR ⌝} {⌜ #[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟ ⌝} {⌜ #AX ⌝}
                                             (subNotIn ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n))
                                             (sub-VAR0 ⌜ a ⌝)
                                             (subNotIn ⌜ a ⌝ ⌜ #CHOOSE (#CS name) (ℂ→C· ℂ₁·) ⌝ (CTerm.closed (#CHOOSE (#CS name) (ℂ→C· ℂ₁·))))
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


-- MOVE to computation
⇓→from-to : {w : 𝕎·} {a b : Term}
              → a ⇓ b at w
              → Σ 𝕎· (λ w' → a ⇓ b from w to w')
⇓→from-to {w} {a} {b} (n , comp) = snd (steps n (a , w)) , n , stepsT→steps {n} {a} {b} {w} comp


-- MOVE to computation
⇓-from-to→⇓ : {w w' : 𝕎·} {a b : Term}
              → a ⇓ b from w to w'
              → a ⇓ b at w
⇓-from-to→⇓ {w} {w'} {a} {b} (n , comp) = n , steps→stepsT' {n} {a} {b} {w} {w'} comp


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


CHOOSE-CS⇛AX : {w : 𝕎·} {name : Name} {t : Term} → CHOOSE (CS name) t ⇛ AX at w
CHOOSE-CS⇛AX {w} {name} {t} w1 e1 = lift (1 , refl)


-- MOVE to computation
IFLE-CHOOSE⇛AX : {w : 𝕎·} {n a : Term} {k j : ℕ} {name : Name} {t : Term}
                  → n ⇛ NUM k at w
                  → a ⇛ NUM j at w
                  → IFLE n a (CHOOSE (CS name) t) AX ⇛ AX at w
IFLE-CHOOSE⇛AX {w} {n} {a} {k} {j} {name} {t} c d =
  ⇛-trans (IFLE⇛₁ d) (⇛-trans (IFLE⇛₂ c) concl)
  where
    concl : IFLE (NUM k) (NUM j) (CHOOSE (CS name) t) AX ⇛ AX at w
    concl with k ≤? j
    ... | yes p = ⇛-trans (IFLE⇛≤ p) CHOOSE-CS⇛AX
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


SEQ-AX⇛₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇛ t at w
SEQ-AX⇛₁ {w} {t} tc w1 e1 = lift (1 , c)
  where
    c : sub AX (shiftUp 0 t) ≡ t
    c rewrite #shiftUp 0 (ct t tc) | subNotIn AX t tc = refl


SEQ-AX⇛ : {w : 𝕎·} {a b : Term}
           → # b
           → a ⇛ AX at w
           → SEQ a b ⇛ b at w
SEQ-AX⇛ {w} {a} {b} cb comp = ⇛-trans (SEQ⇛₁ comp) (SEQ-AX⇛₁ cb)


bound∈ : (i : ℕ) (w : 𝕎·) (name : Name) (n : CTerm) (f : CTerm)
         → ∈Type i w #NAT n
         → ∈Type i w #BAIRE f
         → equalInType i w #BAIRE (#bound name n f) (#bound name n f)
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
                             → NATeq w' (#SEQ (#IFLE n a₁ (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₁))
                                         (#SEQ (#IFLE n a₂ (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₂)))
        aw1 w2 e2 (j , c₁ , c₂) (k , d₁ , d₂) (m , e₁ , e₂) =
          m ,
          ⇛-trans (SEQ-AX⇛ (CTerm.closed (#APPLY f a₁)) (IFLE-CHOOSE⇛AX d₁ c₁)) e₁ ,
          ⇛-trans (SEQ-AX⇛ (CTerm.closed (#APPLY f a₂)) (IFLE-CHOOSE⇛AX d₂ c₂)) e₂

        eqi1 : equalInType i w1 #NAT (#SEQ (#IFLE n a₁ (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₁))
                                     (#SEQ (#IFLE n a₂ (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) #AX) (#APPLY f a₂))
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


-- MOVE to computation
#⇛→#⇓from-to : {w : 𝕎·} {a b : CTerm}
                 → a #⇛ b at w
                 → Σ 𝕎· (λ w' → a #⇓ b from w to w')
#⇛→#⇓from-to {w} {a} {b} comp = ⇓→from-to (lower (comp w (⊑-refl· _)))


-- MOVE to computation
#⇛!→#⇓! : {w : 𝕎·} {a b : CTerm}
                 → a #⇛! b at w
                 → a #⇓! b at w
#⇛!→#⇓! {w} {a} {b} comp = lower (comp w (⊑-refl· _))


-- MOVE to util
→≡snd : {l k : Level} {A : Set l} {B : Set k} {p₁ p₂ : A × B} → p₁ ≡ p₂ → snd p₁ ≡ snd p₂
→≡snd {l} {k} {A} {B} {a₁ , b₁} {a₂ , b₂} e = pair-inj₂ e


-- MOVE to worldDef
≡ᵣ→⊑ : {w1 w2 w3 : 𝕎·} → w1 ⊑· w2 → w2 ≡ w3 → w1 ⊑· w3
≡ᵣ→⊑ {w1} {w2} {w3} e₁ e₂ rewrite e₂ = e₁


-- MOVE to computation
#⇓from-to→⊑ : {w w' : 𝕎·} {a b : CTerm}
               → a #⇓ b from w to w'
               → w ⊑· w'
#⇓from-to→⊑ {w} {w'} {a} {b} (n , comp) = ≡ᵣ→⊑ (steps⊑ w n ⌜ a ⌝) (→≡snd comp)


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



test∈ : (i : ℕ) (w : 𝕎·) (F : CTerm) (name : Name) (n : CTerm) (f : CTerm)
        → compatible· name w Resℂ₀₁
        → ∈Type i w #BAIRE→NAT F
        → ∈Type i w #NAT n
        → ∈Type i w #BAIRE f
        → ∈Type i w (#UNION #NAT #TRUE) (#test name F n f)
test∈ i w F name n f compat ∈F ∈n ∈f =
{--  ≡CTerm→equalInType
    (sym (#UNION≡ Typeℂ₀₁· #TRUE))--}
    (→equalInType-UNION eqTypesNAT eqTypesTRUE (∀𝕎-□Func2 aw gc ∈A))
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
                            #test name F n f #⇛ #INL x at w' × #test name F n f #⇛ #INL y at w' × equalInType i w' #NAT x y
                            ⊎ #test name F n f #⇛ #INR x at w' × #test name F n f #⇛ #INR y at w' × equalInType i w' #TRUE x y)))
    aw w1 e1 gcn (m , c₁ , c₂) = j (lower (gcn w2 e2))
      where
        comp : Σ 𝕎· (λ w2 → (#APPLY F (#bound name n f)) #⇓ (#NUM m) from w1 to w2)
        comp = #⇛→#⇓from-to {w1} {#APPLY F (#bound name n f)} {#NUM m} c₁

        w2 : 𝕎·
        w2 = fst comp

        cp : (#APPLY F (#bound name n f)) #⇓ (#NUM m) from w1 to w2
        cp = snd comp

        e2 : w1 ⊑· w2
        e2 = #⇓from-to→⊑ {_} {_} {#APPLY F (#bound name n f)} {#NUM m} cp

        j : (getChoice· 0 name w2 ≡ just ℂ₀· ⊎ getChoice· 0 name w2 ≡ just ℂ₁·)
            → Σ CTerm (λ x → Σ CTerm (λ y →
                  #test name F n f #⇛ #INL x at w1 × #test name F n f #⇛ #INL y at w1 × equalInType i w1 #NAT x y
                  ⊎ #test name F n f #⇛ #INR x at w1 × #test name F n f #⇛ #INR y at w1 × equalInType i w1 #TRUE x y))
        j (inj₁ z) = #NUM m , #NUM m , inj₁ ({!!} , {!!} , NUM-equalInType-NAT i w1 m)
        j (inj₂ z) = #AX , #AX , inj₂ ({!!} , {!!} , →equalInType-TRUE i)


-- Do we need to constrain F's type to be in (BAIRE→NAT!)? -- No, doesn't make sense: what function is going to inhabit that type?

-- Check what world (#APPLY F (#bound name n f)) ends up in and name's value in that world
-- and compare it with with ℂ₀ before instantiating the conclusion
-- Because we used NAT, this requires choices to be numbers (should be QTNAT in the union)

\end{code}
