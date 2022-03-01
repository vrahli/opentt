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


-- TODO: the name should be a fresh name, that does not occur in F
-- TODO: need union types?

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
            | lowerVarsApp (fvars (shiftUp 0 (CTerm.cTerm f))) [ 1 ]
            | #shiftUp 0 f
            | lowerVars-fvars-CTerm≡[] f = refl


#BOUND : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#BOUND name n f =
  #LAMBDA (#[0]SEQ (#[0]IF-THEN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟))
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
                     → #APPLY (#BOUND name n f) a #⇛! #SEQ (#IF-THEN (#LE n a) (#CHOOSE (#CS name) (ℂ→C· ℂ₁·))) (#APPLY f a) at w
#⇛!-#APPLY-#BOUND w name n f a w1 e1
  = lift (1 , →≡pair (→sub-SEQ {⌜ a ⌝}
                                 {⌜ #[0]IF-THEN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟) ⌝}
                                 {⌜ #[0]APPLY ⌞ f ⌟ #[0]VAR ⌝}
                                 {⌜ #IF-THEN (#LE n a) (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)) ⌝}
                                 {⌜ #APPLY f a ⌝}
                                 (CTerm.closed a) (CTerm0.closed (#[0]APPLY ⌞ f ⌟ #[0]VAR))
                                 (→sub-IF-THEN {⌜ a ⌝} {⌜ #[0]LE ⌞ n ⌟ #[0]VAR ⌝}
                                                {⌜ #[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟ ⌝} {⌜ #LE n a ⌝}
                                                {⌜ #CHOOSE (#CS name) (ℂ→C· ℂ₁·) ⌝}
                                                (CTerm.closed a)
                                                (CTerm0.closed (#[0]CHOOSE (#[0]CS name) ⌞ ℂ→C· ℂ₁· ⌟))
                                                (→sub-LE {⌜ a ⌝} {⌜ n ⌝} {⌜ #[0]VAR ⌝} {⌜ n ⌝} {⌜ a ⌝} (subNotIn ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n)) (sub-VAR0 ⌜ a ⌝))
                                                (subNotIn ⌜ a ⌝ ⌜ #CHOOSE (#CS name) (ℂ→C· ℂ₁·) ⌝ (CTerm.closed (#CHOOSE (#CS name) (ℂ→C· ℂ₁·)))))
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
        eqi1 : equalInType i w1 #NAT (#SEQ (#IF-THEN (#LE n a₁) (#CHOOSE (#CS name) (ℂ→C· ℂ₁·))) (#APPLY f a₁))
                                     (#SEQ (#IF-THEN (#LE n a₂) (#CHOOSE (#CS name) (ℂ→C· ℂ₁·))) (#APPLY f a₂))
        eqi1 = {!!} -- This does not work with our current nats because the world changes

--∈Type i w #NAT n
--∈Type i w #NAT a

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
