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
open import mod


module continuity {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                  (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                  (X : ChoiceExt W C K G)
                  (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)

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

open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)


-- turns 'f' into λy.(if n < y then name:=ℂ₁);f(y)
-- ℂ₀ is treated as true here, and ℂ₁ as false
bound : (name : Name) (n : Term) (f : Term) → Term
bound name n f = LAMBDA (SEQ (IF-THEN (LE n (VAR 0)) (CHOOSE (CS name) (ℂ→T ℂ₁·))) (APPLY f (VAR 0)))


-- We assume that initially name contains ℂ₀
test : (name : Name) (F : Term) (n : Term) (f : Term) → Term
test name F n f = LET (APPLY F (bound name n f))
                      (LET (IFC0 (APPLY (CS name) (NUM 0)) (VAR 0) AX) -- We check whether 'name' contains ℂ₀
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
#[0]IF-THEN : CTerm0 → CTerm0 → CTerm0
#[0]IF-THEN a b = ct0 (IF-THEN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] IF-THEN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-IF-THEN ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))


-- MOVE to terms
#[0]LE : CTerm0 → CTerm0 → CTerm0
#[0]LE a b = ct0 (LE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LE ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-NEG (LT ⌜ b ⌝ ⌜ a ⌝) = ⊆→⊆? {fvars ⌜ b ⌝ ++ fvars ⌜ a ⌝ } {[ 0 ]}
                                               (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b))
                                                    (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a)))


-- MOVE to terms
#[0]CHOOSE : CTerm0 → CTerm0 → CTerm0
#[0]CHOOSE a b = ct0 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))



#bound : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#bound name n f = ct (bound name ⌜ n ⌝ ⌜ f ⌝) c
  where
    c : # bound name ⌜ n ⌝ ⌜ f ⌝
    c rewrite CTerm.closed n | CTerm.closed f
            | #shiftUp 0 (ℂ→C· ℂ₁·)
            | lowerVars-fvars-CTerm≡[] (ℂ→C· ℂ₁·)
            | lowerVarsApp (fvars (shiftUp 0 (CTerm.cTerm f))) [ 1 ]
            | #shiftUp 0 f
            | lowerVars-fvars-CTerm≡[] f = refl


#BOUND : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#BOUND name n f =
  #LAMBDA (#[0]SEQ (#[0]IF-THEN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟))
                   (#[0]APPLY ⌞ f ⌟ #[0]VAR))

#bound≡ : (name : Name) (n : CTerm) (f : CTerm) → #bound name n f ≡ #BOUND name n f
#bound≡ name n f = CTerm≡ refl



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


bound∈ : (i : ℕ) (w : 𝕎·) (name : Name) (n : CTerm) (f : CTerm)
         → ∈Type i w #NAT n
         → ∈Type i w #BAIRE f
         → equalInType i w #BAIRE (#bound name n f) (#bound name n f)
bound∈ i w name n f ∈n ∈f =
  ≡CTerm→equalInTypeₗ (sym (#bound≡ name n f)) (≡CTerm→equalInTypeᵣ (sym (#bound≡ name n f)) (≡CTerm→equalInType (sym #BAIRE≡) {!eqi!}))
  where
    eqi : equalInType i w (#FUN #NAT #NAT) (#BOUND name n f) (#BOUND name n f)
    eqi = {!!}


APPLY-bound∈ : (i : ℕ) (w : 𝕎·) (F : CTerm) (name : Name) (n : CTerm) (f : CTerm)
               → ∈Type i w #BAIRE→NAT F
               → ∈Type i w #NAT n
               → ∈Type i w #BAIRE f
               → ∈Type i w #NAT (#APPLY F (#bound name n f))
APPLY-bound∈ i w F name n f ∈F ∈n ∈f =
  equalInType-FUN→
    {i} {w} {#BAIRE} {#NAT} {F} {F} ∈F w (⊑-refl· _) (#bound name n f) (#bound name n f)
    (bound∈ i w name n f ∈n ∈f)

{-- ≡CTerm→equalInType (sym #BAIRE→NAT≡) (equalInType-FUN aw1 aw2 aw3)
  where
    aw1 : ∀𝕎 w (λ w' _ → isType i w' #BAIRE)
    aw1 w1 e1 = eqTypesBAIRE

    aw2 : ∀𝕎 w (λ w' _ → isType i w' #NAT)
    aw2 w1 e1 = eqTypesNAT

    aw3 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #BAIRE a₁ a₂
                        → equalInType i w' #NAT (#APPLY (#APPLY F (#bound name n f)) a₁) (#APPLY (#APPLY F (#bound name n f)) a₂))
    aw3 w1 e1 a₁ a₂ ea = {!!}
      where
        eqn : equalInType i w1 #NAT (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY F f) a₂)
        eqn = equalInType-FUN→ {i} {w1} {#BAIRE} {#NAT} {#APPLY F f} {#APPLY F f} {!!} w1 (⊑-refl· _)  a₁ a₂ ea
--}
\end{code}
