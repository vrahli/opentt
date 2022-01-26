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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar


module not_lpo {L : Level} (W : PossibleWorlds {L})
               (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
               (CB : ChoiceBar W C G N F P E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
open import choiceBarDef(W)(C)(G)(N)(F)(P)(E)(CB)
open import computation(W)(C)(G)
open import bar(W)(C)(G)(N)(F)(P)
open import barI(W)(C)(G)(N)(F)(P)
open import theory(W)(C)(G)(N)(F)(P)(E)
open import props0(W)(C)(G)(N)(F)(P)(E)
open import ind2(W)(C)(G)(N)(F)(P)(E)

open import type_sys_props_nat(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_qnat(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_lt(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_qlt(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_free(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_pi(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_sum(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_set(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_eq(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_union(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_tsquash(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_ffdefs(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_lift(W)(C)(G)(N)(F)(P)(E)

open import props1(W)(C)(G)(N)(F)(P)(E)
open import props2(W)(C)(G)(N)(F)(P)(E)
open import props3(W)(C)(G)(N)(F)(P)(E)
open import lem_props(W)(C)(G)(N)(F)(P)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar) -- this is the one where a function is not recognized as terminating, but does not break the bar abstraction
-- open import type_sys_props_nat (bar)
-- open import type_sys_props_qnat (bar)
-- open import type_sys_props_lt (bar)
-- open import type_sys_props_qlt (bar)
-- open import type_sys_props_free (bar)
-- open import type_sys_props_pi (bar)
-- open import type_sys_props_sum (bar)
-- open import type_sys_props_set (bar)
-- open import type_sys_props_eq (bar)
-- open import type_sys_props_union (bar)
-- open import type_sys_props_tsquash (bar)
-- open import type_sys_props_ffdefs (bar)
-- open import props1 (bar)
-- open import terms (bar)
\end{code}




\begin{code}[hide]
BOOL : Term
BOOL = UNION TRUE TRUE


#BOOL : CTerm
#BOOL = ct BOOL refl


#BOOL≡ : #BOOL ≡ #UNION #TRUE #TRUE
#BOOL≡ = CTerm≡ refl


NAT→BOOL : Term
NAT→BOOL = FUN NAT BOOL


#NAT→BOOL : CTerm
#NAT→BOOL = ct NAT→BOOL refl


#NAT→BOOL≡ : #NAT→BOOL ≡ #FUN #NAT #BOOL
#NAT→BOOL≡ = CTerm≡ refl


ASSERT : Term → Term
ASSERT t = DECIDE t TRUE FALSE


LPO : Term
LPO = PI NAT→BOOL (SQUASH (UNION (SUM NAT (ASSERT (APPLY (VAR 1) (VAR 0))))
                                  (PI NAT (NEG (ASSERT (APPLY (VAR 1) (VAR 0)))))))


#LPO : CTerm
#LPO =  ct LPO c
  where
    c : # LPO
    c = refl


record CTerm1 : Set where
  constructor ct1
  field
    cTerm  : Term
    closed : #[ (0 ∷ [ 1 ]) ] cTerm


instance
  CTerm1ToTerm : ToTerm CTerm1
  ⌜_⌝ {{CTerm1ToTerm}} t = CTerm1.cTerm t


CTerm→CTerm1 : CTerm → CTerm1
CTerm→CTerm1 (ct t c) = ct1 t c'
  where
    c' : #[ 0 ∷ [ 1 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm1 : fromCTerm CTerm1
  ⌞_⌟ {{CTermToCTerm1}} t = CTerm→CTerm1 t


#[1]APPLY : CTerm1 → CTerm1 → CTerm1
#[1]APPLY a b = ct1 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


fvars-ASSERT : (t : Term) → fvars (ASSERT t) ≡ fvars t
fvars-ASSERT t rewrite ++[] (fvars t) = refl


#ASSERT : CTerm → CTerm
#ASSERT a = ct (ASSERT ⌜ a ⌝) c
  where
    c : # ASSERT ⌜ a ⌝
    c rewrite fvars-ASSERT ⌜ a ⌝ = CTerm.closed a


#[0]ASSERT : CTerm0 → CTerm0
#[0]ASSERT a = ct0 (ASSERT ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ASSERT ⌜ a ⌝
    c rewrite fvars-ASSERT ⌜ a ⌝ = CTerm0.closed a


#[1]ASSERT : CTerm1 → CTerm1
#[1]ASSERT a = ct1 (ASSERT ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] ASSERT ⌜ a ⌝
    c rewrite fvars-ASSERT ⌜ a ⌝ = CTerm1.closed a


#[1]NEG : CTerm1 → CTerm1
#[1]NEG a = ct1 (NEG ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] NEG ⌜ a ⌝
    c rewrite fvars-NEG ⌜ a ⌝ = CTerm1.closed a


[0]⊆[0,1] : [ 0 ] ⊆ (0 ∷ [ 1 ])
[0]⊆[0,1] (here px) rewrite px = here refl


[1]⊆[0,1] : [ 1 ] ⊆ (0 ∷ [ 1 ])
[1]⊆[0,1] (here px) rewrite px = there (here refl)


#[1]VAR0 : CTerm1
#[1]VAR0 = ct1 (VAR 0) c
  where
    c : #[ 0 ∷ [ 1 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1]


#[1]VAR1 : CTerm1
#[1]VAR1 = ct1 (VAR 1) c
  where
    c : #[ 0 ∷ [ 1 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1]


lowerVars-fvars-[0,1] : {l : List Var}
                        → l ⊆ (0 ∷ [ 1 ])
                        → lowerVars l ⊆ [ 0 ]
lowerVars-fvars-[0,1] {0 ∷ l} h x = lowerVars-fvars-[0,1] (λ z → h (there z)) x
lowerVars-fvars-[0,1] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ [])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ []) →  x₁ ∈ [ 0 ]
    i (there (here px)) = here (suc-injective px)
lowerVars-fvars-[0,1] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1] (λ z → h (there z)) x


#[0]SUM : CTerm0 → CTerm1 → CTerm0
#[0]SUM a b = ct0 (SUM ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] SUM ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))


#[0]PI : CTerm0 → CTerm1 → CTerm0
#[0]PI a b = ct0 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))


#[0]LPO-left : CTerm0
#[0]LPO-left = #[0]SUM #[0]NAT (#[1]ASSERT (#[1]APPLY #[1]VAR1 #[1]VAR0))


#[0]LPO-right : CTerm0
#[0]LPO-right = #[0]PI #[0]NAT (#[1]NEG (#[1]ASSERT (#[1]APPLY #[1]VAR1 #[1]VAR0)))


#LPO-left : CTerm → CTerm
#LPO-left f = #SUM #NAT (#[0]ASSERT (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#LPO-right : CTerm → CTerm
#LPO-right f = #PI #NAT (#[0]NEG (#[0]ASSERT (#[0]APPLY ⌞ f ⌟ #[0]VAR)))


#LPO-PI : CTerm
#LPO-PI = #PI #NAT→BOOL (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))


#LPO≡#PI : #LPO ≡ #LPO-PI
#LPO≡#PI = CTerm≡ refl


isTypeBOOL : (w : 𝕎·) (n : ℕ) → isType n w #BOOL
isTypeBOOL w n rewrite #BOOL≡ = eqTypesUNION← eqTypesTRUE eqTypesTRUE


isType-#NAT→BOOL : (w : 𝕎·) (n : ℕ) → isType n w #NAT→BOOL
isType-#NAT→BOOL w n rewrite #NAT→BOOL≡ = eqTypesFUN← eqTypesNAT (isTypeBOOL w n)


sub0-#[0]UNION : (a : CTerm) (t u : CTerm0)
                 → sub0 a (#[0]UNION t u) ≡ #UNION (sub0 a t) (sub0 a u)
sub0-#[0]UNION a t u = CTerm≡ refl


≡UNION : {a b c d : Term} → a ≡ b → c ≡ d → UNION a c ≡ UNION b d
≡UNION {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl


≡SUM : {a b c d : Term} → a ≡ b → c ≡ d → SUM a c ≡ SUM b d
≡SUM {a} {b} {c} {d} e f rewrite e | f = refl


≡ASSERT : {a b : Term} → a ≡ b → ASSERT a ≡ ASSERT b
≡ASSERT {a} {b} e rewrite e = refl


≡NEG : {a b : Term} → a ≡ b → NEG a ≡ NEG b
≡NEG {a} {b} e rewrite e = refl


≡PI : {a b c d : Term} → a ≡ b → c ≡ d → PI a c ≡ PI b d
≡PI {a} {b} {c} {d} e f rewrite e | f = refl


≡sub0-#[0]SQUASH : (a : CTerm) (t : CTerm0) (u : CTerm)
                   → sub0 a t ≡ u
                   → sub0 a (#[0]SQUASH t) ≡ #SQUASH u
≡sub0-#[0]SQUASH a t u e rewrite sym e = sub0-#[0]SQUASH a t


sub0-squash-union-LPO : (a : CTerm) → sub0 a (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))
                                       ≡ #SQUASH (#UNION (#LPO-left a) (#LPO-right a))
sub0-squash-union-LPO a =
  ≡sub0-#[0]SQUASH a (#[0]UNION #[0]LPO-left #[0]LPO-right) (#UNION (#LPO-left a) (#LPO-right a))
                   (CTerm≡ (≡UNION (≡SUM refl (≡ASSERT (→≡APPLY e refl))) (≡PI refl (≡NEG (≡ASSERT (→≡APPLY e refl))))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


sub0-ASSERT-APPLY-LPO : (a b : CTerm) → sub0 a (#[0]ASSERT (#[0]APPLY ⌞ b ⌟ #[0]VAR)) ≡ #ASSERT (#APPLY b a)
sub0-ASSERT-APPLY-LPO a b = CTerm≡ (≡ASSERT (→≡APPLY x y))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl


sub0-#[0]NEG : (a : CTerm) (t : CTerm0) → sub0 a (#[0]NEG t) ≡ #NEG (sub0 a t)
sub0-#[0]NEG a t = CTerm≡ refl


sub0-NEG-ASSERT-APPLY-LPO : (a b : CTerm) → sub0 a (#[0]NEG (#[0]ASSERT (#[0]APPLY ⌞ b ⌟ #[0]VAR))) ≡ #NEG (#ASSERT (#APPLY b a))
sub0-NEG-ASSERT-APPLY-LPO a b
  rewrite sub0-#[0]NEG a (#[0]ASSERT (#[0]APPLY ⌞ b ⌟ #[0]VAR)) | sub0-ASSERT-APPLY-LPO a b
  = CTerm≡ (≡NEG (≡ASSERT (→≡APPLY x y)))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl



step-⇓-ASSERT : {w : 𝕎·} {a b : Term}
                 → step a w ≡ just b
                 → ASSERT a ⇓ ASSERT b at w
step-⇓-ASSERT {w} {NAT} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {QNAT} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {LT a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {QLT a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {NUM x} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {PI a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {LAMBDA a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {APPLY a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT (APPLY a a₁)) w ≡ ASSERT b
    z rewrite comp = refl
step-⇓-ASSERT {w} {SUM a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {PAIR a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {SET a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {UNION a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {INL a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {INR a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {DECIDE a a₁ a₂} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT (DECIDE a a₁ a₂)) w ≡ ASSERT b
    z rewrite comp = refl
step-⇓-ASSERT {w} {EQ a a₁ a₂} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {AX} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {FREE} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {CS x} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {TSQUASH a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {DUM a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {FFDEFS a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {UNIV x} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {LIFT a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {LOWER a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT {w} {SHRINK a} {b} comp rewrite sym (just-inj comp) = 0 , refl



steps-⇓-ASSERT : {w : 𝕎·} (n : ℕ) {a b : Term}
                 → steps n a w ≡ b
                 → ASSERT a ⇓ ASSERT b at w
steps-⇓-ASSERT {w} 0 {a} {b} comp rewrite comp = 0 , refl
steps-⇓-ASSERT {w} (suc n) {a} {b} comp with step⊎ a w
... | inj₁ (u , p) rewrite p = ⇓-trans (step-⇓-ASSERT p) (steps-⇓-ASSERT n comp)
... | inj₂ p rewrite p | comp = 0 , refl


⇓-ASSERT-INL : {w : 𝕎·} {a x : Term}
           → a ⇓ INL x at w
           → ASSERT a ⇓ TRUE at w
⇓-ASSERT-INL {w} {a} {x} comp = ⇓-trans (steps-⇓-ASSERT (fst comp) (snd comp)) (1 , refl)


#⇛-ASSERT-INL : {w : 𝕎·} {a x : CTerm}
             → a #⇛ #INL x at w
             → #ASSERT a #⇛ #TRUE at w
#⇛-ASSERT-INL {w} {a} {x} comp w' e = lift (⇓-ASSERT-INL (lower (comp w' e)))


⇓-ASSERT-INR : {w : 𝕎·} {a x : Term}
           → a ⇓ INR x at w
           → ASSERT a ⇓ FALSE at w
⇓-ASSERT-INR {w} {a} {x} comp = ⇓-trans (steps-⇓-ASSERT (fst comp) (snd comp)) (1 , refl)


#⇛-ASSERT-INR : {w : 𝕎·} {a x : CTerm}
             → a #⇛ #INR x at w
             → #ASSERT a #⇛ #FALSE at w
#⇛-ASSERT-INR {w} {a} {x} comp w' e = lift (⇓-ASSERT-INR (lower (comp w' e)))


equalInType-BOOL→equalTypes-ASSERT : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL a b
                                      → equalTypes n w (#ASSERT a) (#ASSERT b)
equalInType-BOOL→equalTypes-ASSERT {n} {w} {a} {b} eqb =
  EQTBAR (Bar.∀𝕎-inBarFunc barI j i)
  where
    i : inbar w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                        → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' #TRUE x y)
                           ⊎
                           (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' #TRUE x y))))
    i = equalInType-UNION→ eqb

    j : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y
                      → (a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType n w' #TRUE x y)
                         ⊎
                         (a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType n w' #TRUE x y)))
                      → equalTypes n w' (#ASSERT a) (#ASSERT b))
    j w' e (x , y , inj₁ (c₁ , c₂ , eqi)) = equalTypes-#⇛-left-right-rev (#⇛-ASSERT-INL {w'} {a} {x} c₁) (#⇛-ASSERT-INL {w'} {b} {y} c₂) eqTypesTRUE
    j w' e (x , y , inj₂ (c₁ , c₂ , eqi)) = equalTypes-#⇛-left-right-rev (#⇛-ASSERT-INR {w'} {a} {x} c₁) (#⇛-ASSERT-INR {w'} {b} {y} c₂) eqTypesFALSE


→equalTypes-#LPO-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                         → equalInType n w #NAT→BOOL a₁ a₂
                         → equalTypes n w (#LPO-left a₁) (#LPO-left a₂)
→equalTypes-#LPO-left {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → eqTypesNAT) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT-APPLY-LPO a a₁ | sub0-ASSERT-APPLY-LPO b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT (#APPLY a₁ a)) (#ASSERT (#APPLY a₂ b))
        aw2 = equalInType-BOOL→equalTypes-ASSERT eqb


→equalTypes-#LPO-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT→BOOL a₁ a₂
                          → equalTypes n w (#LPO-right a₁) (#LPO-right a₂)
→equalTypes-#LPO-right {n} {w} {a₁} {a₂} eqt =
  eqTypesPI← (λ w' _ → eqTypesNAT) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT a b → equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ eqt

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT a b)
                       → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                          (sub0 b (#[0]NEG (#[0]ASSERT (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR)))))
    aw1 w' e a b ea rewrite sub0-NEG-ASSERT-APPLY-LPO a a₁ | sub0-NEG-ASSERT-APPLY-LPO b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#NEG (#ASSERT (#APPLY a₁ a))) (#NEG (#ASSERT (#APPLY a₂ b)))
        aw2 = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT eqb)



isTypeLPO-PI : (w : 𝕎·) (n : ℕ) → isType n w #LPO-PI
isTypeLPO-PI w n =
  eqTypesPI← {w} {n}
              {#NAT→BOOL} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)}
              {#NAT→BOOL} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)}
              (λ w' e → isType-#NAT→BOOL w' n)
              aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT→BOOL a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)))
                                         (sub0 a₂ (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))))
    aw w' e a₁ a₂ eqb rewrite sub0-squash-union-LPO a₁ | sub0-squash-union-LPO a₂ = eqt
      where
        eqt1 : equalTypes n w' (#LPO-left a₁) (#LPO-left a₂)
        eqt1 = →equalTypes-#LPO-left eqb

        eqt2 : equalTypes n w' (#LPO-right a₁) (#LPO-right a₂)
        eqt2 = →equalTypes-#LPO-right eqb

        eqt : equalTypes n w' (#SQUASH (#UNION (#LPO-left a₁) (#LPO-right a₁))) (#SQUASH (#UNION (#LPO-left a₂) (#LPO-right a₂)))
        eqt = eqTypesSQUASH← (eqTypesUNION← eqt1 eqt2)



isTypeLPO : (w : 𝕎·) (n : ℕ) → isType n w #LPO
isTypeLPO w n rewrite #LPO≡#PI = isTypeLPO-PI w n


isTypeNegLPO : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #LPO)
isTypeNegLPO w n = eqTypesNEG← (isTypeLPO w n)



Σchoice : (n : Name) (k : ℂ·) → Term
Σchoice n k = SUM NAT (EQ (APPLY (CS n) (VAR 0)) (ℂ→T k) typeℂ₀₁)



#Σchoice : (n : Name) (k : ℂ·) → CTerm
#Σchoice n k = ct (Σchoice n k) c
  where
    c : # (Σchoice n k)
    c rewrite #-typeℂ₀₁ | #-ℂ→T k = refl


{--
#Σchoice≡ : (n : Name) (k : ℂ·) → #Σchoice n k ≡ #SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS n) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)
#Σchoice≡ n k = CTerm≡ refl


sub0-#Σchoice-body≡ : (a : CTerm) (c : Name) (k : ℂ·)
                      → sub0 a (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)
                         ≡ #EQ (#APPLY (#CS c) a) (ℂ→C· k) Typeℂ₀₁·
sub0-#Σchoice-body≡ a c k = CTerm≡ (→≡EQ (→≡APPLY refl (shiftDownUp ⌜ a ⌝ 0))
                                          (subNotIn ⌜ a ⌝ _ (CTerm.closed (ℂ→C· k)))
                                          (subNotIn ⌜ a ⌝ _ (CTerm.closed Typeℂ₀₁·)))


sat→equalInType-Typeℂ₀₁· : (i : ℕ) (w : 𝕎·) (k : ℂ·)
                            → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                            → equalInType i w Typeℂ₀₁· (ℂ→C· k) (ℂ→C· k)
sat→equalInType-Typeℂ₀₁· i w k (n , inj₁ x) rewrite x = ℂ₀∈Typeℂ₀₁· i w
sat→equalInType-Typeℂ₀₁· i w k (n , inj₂ y) rewrite y = ℂ₁∈Typeℂ₀₁· i w



comp-Resℂ→inbar-weakℂ₀₁ : {c : Name} {w : 𝕎·} (n : ℕ)
                           → compatible· c w Resℂ
                           → inbar w (λ w' _ → weakℂ₀₁M w' (getT n c))
comp-Resℂ→inbar-weakℂ₀₁ {c} {w} n comp = Bar.∀𝕎-inBarFunc barI aw j1
  where
    j1 : inbar w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℂ· (λ t → getChoice· n c w'' ≡ just t))))
    j1 = inbar-choice· w c n Resℂ comp

    aw : ∀𝕎 w (λ w2 e2 → ∀𝕎 w2 (λ w3 _ → Lift (lsuc L) (Σ ℂ· (λ t → getChoice· n c w3 ≡ just t))) → weakℂ₀₁M w2 (getT n c))
    aw w2 e2 h w3 e3 rewrite snd (lower (h w3 e3)) = lift (ℂ→T t , refl , z st)
      where
        t : ℂ·
        t = fst (lower (h w3 e3))

        st : ·ᵣ Resℂ n t
        st = getChoiceCompatible· c Resℂ w3 n t (⊑-compatible· (⊑-trans· e2 e3) comp) (snd (lower (h w3 e3)))

        z : (t ≡ ℂ₀· ⊎ t ≡ ℂ₁·)
            → (ℂ→T (fst (lower (h w3 e3))) ⇓ Tℂ₀ at w3
                ⊎ ℂ→T (fst (lower (h w3 e3))) ⇓ Tℂ₁ at w3)
        z (inj₁ x) rewrite x = inj₁ (0 , refl)
        z (inj₂ x) rewrite x = inj₂ (0 , refl)



equalTypes-#Σchoice-body : (i : ℕ) (w : 𝕎·) (c : Name) (k : ℂ·)
                           → compatible· c w Resℂ
                           → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                           → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                           → equalInType i w' #NAT a₁ a₂
                                           → equalTypes i w' (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k) Typeℂ₀₁·)
                                                              (#EQ (#APPLY (#CS c) a₂) (ℂ→C· k) Typeℂ₀₁·))
equalTypes-#Σchoice-body i w c k comp sat w' e' a₁ a₂ ea =
  eqTypesEQ← (Typeℂ₀₁-isType· i w') aw1 aw2
{--  eqTypesEQ← eqTypesQNAT aw1 aw2 --}
  where
--    j : inbar w' (λ w' _ → #strongMonEq w' a₁ a₂)
--    j = equalInType-NAT→ i w' a₁ a₂ ea

    aw1 : equalInType i w' Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
    aw1 = equalInType-local (Bar.∀𝕎-inBarFunc barI aw1' (equalInType-NAT→ i w' a₁ a₂ ea))
      where
        aw1' : ∀𝕎 w' (λ w'' e'' → #strongMonEq w'' a₁ a₂ → equalInType i w'' Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂))
        aw1' w1 e1 (n , c₁ , c₂) = equalInType-#⇛-LR-rev (#⇛-APPLY-CS {w1} {a₁} {#NUM n} c c₁) (#⇛-APPLY-CS {w1} {a₂} {#NUM n} c c₂) eqi
          where
            j2 : inbar w1 (λ w' _ → weakℂ₀₁M w' (getT n c))
            j2 = comp-Resℂ→inbar-weakℂ₀₁ n (⊑-compatible· (⊑-trans· e' e1) comp)

            eqi : ∈Type i w1 Typeℂ₀₁· (#APPLY (#CS c) (#NUM n))
            eqi = →∈Typeℂ₀₁· i j2
            -- use choice-Typeℂ₀₁

 {--→equalInType-QNAT i w' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂) (Bar.inBar-idem barI (Bar.∀𝕎-inBarFunc barI aw11 j))
      where
        aw11 : ∀𝕎 w' (λ w'' e'' → #strongMonEq w'' a₁ a₂
                                 → inbar w'' (↑wPred' (λ w''' e → #weakMonEq w''' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)) e''))
        aw11 w'' e'' (m , c₁ , c₂) =
          inbar-wPred'-#weakMonEq w' w'' e'' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
                                  (→inbar-#weakMonEq-APPLY-CS w'' a₁ a₂ m c c₁ c₂ (inbar-#weakMonEq-APPLY-CS i w'' c m (⊑-compatible· (⊑-trans· e' e'') comp)))--}

    aw2 : equalInType i w' Typeℂ₀₁· (ℂ→C· k) (ℂ→C· k)
    aw2 = sat→equalInType-Typeℂ₀₁· i w' k sat



equalTypes-#Σchoice-body-sub0 : (i : ℕ) (w : 𝕎·) (c : Name) (k : ℂ·)
                                → compatible· c w Resℂ
                                → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                                → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                                → equalInType i w' #NAT a₁ a₂
                                                → equalTypes i w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁))
                                                                   (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)))
equalTypes-#Σchoice-body-sub0 i w c k comp sat w' e' a₁ a₂ ea rewrite sub0-#Σchoice-body≡ a₁ c k | sub0-#Σchoice-body≡ a₂ c k =
  equalTypes-#Σchoice-body i w c k comp sat w' e' a₁ a₂ ea



equalInType-#Σchoice : {n i : ℕ} (p : i < n) (w : 𝕎·) (c : Name) (k : ℂ·)
                       → compatible· c w Resℂ
                       → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                       → equalInType n w (#UNIV i) (#Σchoice c k) (#Σchoice c k)
equalInType-#Σchoice {n} {i} p w c k comp sat rewrite #Σchoice≡ c k =
  equalTypes→equalInType-UNIV
    p
    (eqTypesSUM← (λ w' e' → eqTypesNAT) (equalTypes-#Σchoice-body-sub0 i w c k comp sat))



getChoice→equalInType-#Σchoice-aux2 : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℂ·} (i : ℕ)
                                      → ·ᵣ Resℂ n k
                                       → #APPLY (#CS name) (#NUM n) #⇛ ℂ→C· k at w
                                       → equalInType
                                           i w
                                           (#EQ (#APPLY (#CS name) (#NUM n)) (ℂ→C· k) Typeℂ₀₁·)
                                           #AX #AX
getChoice→equalInType-#Σchoice-aux2 {n} {name} {w} {k} i sat g =
  equalInType-EQ (Typeℂ₀₁-isType· i w) (Bar.∀𝕎-inBar barI aw)
  where
    aw : ∀𝕎 w (λ w' e → EQeq (#APPLY (#CS name) (#NUM n)) (ℂ→C· k) (equalInType i w' Typeℂ₀₁·) w' #AX #AX)
    aw w' e = #compAllRefl #AX w' ,
              #compAllRefl #AX w' ,
              equalInType-#⇛-left-rev (∀𝕎-mon e g) (sat→equalInType-Typeℂ₀₁· i w' k (0 , sat)) --→equalInType-QNAT i w' (#APPLY (#CS name) (#NUM n)) (ℂ→C· k) (Bar.∀𝕎-inBar barI aw')
      where
--         aw' : ∀𝕎 w' (λ w'' _ → #weakMonEq w'' (#APPLY (#CS name) (#NUM n)) (ℂ→C· k))
--         aw' w2 e2 w3 e3 = lift (k , step-⇓-trans (lower (g w3 (⊑-trans· e (⊑-trans· e2 e3)))) (⇓-refl (NUM k) w3) , ⇓-refl (NUM k) w3)


getChoice→equalInType-#Σchoice-aux1 : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℂ·} (i : ℕ)
                                       → ·ᵣ Resℂ n k
                                       → #APPLY (#CS name) (#NUM n) #⇛ ℂ→C· k at w
                                       → equalInType
                                           i w
                                           (sub0 (#NUM n) (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁))
                                           #AX #AX
getChoice→equalInType-#Σchoice-aux1 {n} {name} {w} {k} i sat g rewrite sub0-#Σchoice-body≡ (#NUM n) name k =
  getChoice→equalInType-#Σchoice-aux2 i sat g


getChoice→equalInType-#Σchoice-aux : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℂ·} (i : ℕ)
                                      → compatible· name w Resℂ
                                      → ·ᵣ Resℂ n k
                                      → #APPLY (#CS name) (#NUM n) #⇛ ℂ→C· k at w
                                      → equalInType
                                           i w
                                           (#SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁))
                                           (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
getChoice→equalInType-#Σchoice-aux {n} {name} {w} {k} i comp sat g =
  equalInType-SUM
    {i} {w} {#NAT} {#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁}
    (eqTypes-mon (uni i) eqTypesNAT)
    (equalTypes-#Σchoice-body-sub0 i w name k comp (0 , sat))
    j
  where
    j : inbar w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                 (λ a b ea → equalInType i w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)))
                                 w'
                                 (#PAIR (#NUM n) #AX)
                                 (#PAIR (#NUM n) #AX))
    j = Bar.∀𝕎-inBar barI (λ w1 e1 → #NUM n , #NUM n , #AX , #AX ,
                                       NUM-equalInType-NAT i w1 n ,
                                       #compAllRefl (#PAIR (#NUM n) #AX) w1 ,
                                       #compAllRefl (#PAIR (#NUM n) #AX) w1 ,
                                       getChoice→equalInType-#Σchoice-aux1 i sat (∀𝕎-mon e1 g))
-- This last one is not true with references, but can be made true if we have a way to "freeze" a reference permanently,
-- and here 0 was "frozen"


getChoice→equalInType-#Σchoice : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℂ·} (i : ℕ)
                                  → compatible· name w Resℂ
                                  → ·ᵣ Resℂ n k
                                  → #APPLY (#CS name) (#NUM n) #⇛ ℂ→C· k at w
                                  → equalInType i w (#Σchoice name k) (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
getChoice→equalInType-#Σchoice {n} {name} {w} {k} i comp sat g rewrite #Σchoice≡ name k =
  getChoice→equalInType-#Σchoice-aux i comp sat g



{--
steps-APPLY-cs-forward : (w : 𝕎·) (n m : ℕ) (a b v : Term) (c : Name)
                         → isValue v
                         → steps n a w ≡ b
                         → steps m (APPLY (CS c) a) w ≡ v
                         → APPLY (CS c) b ⇓ v at w
steps-APPLY-cs-forward w 0 m a b v c isv c₁ c₂ rewrite c₁ = m , c₂
steps-APPLY-cs-forward w (suc n) 0 a b v c isv c₁ c₂ rewrite (sym c₂) = {!!} --⊥-elim isv
steps-APPLY-cs-forward w (suc n) (suc m) a b v c isv c₁ c₂ with step⊎ a w
... | inj₁ (u , p) rewrite p with is-NUM a
...                          | inj₁ (k , q) rewrite q | sym (just-inj p) | stepsVal (NUM k) w n tt | sym c₁ = suc m , c₂
...                          | inj₂ q rewrite step-APPLY-CS-¬NUM c a u w q p = steps-APPLY-cs-forward w n m u b v c isv c₁ c₂
steps-APPLY-cs-forward w (suc n) (suc m) a b v c isv c₁ c₂ | inj₂ p rewrite p | c₁ = suc m , c₂
--}



¬equalInType-#Σchoice : (i : ℕ) (w : 𝕎·) (r : Res) (c : Name) (x y : CTerm) {k1 : ℂ·}
                        → isValue (ℂ→T (Res.def r))
                        → isValue (ℂ→T k1)
                        → ¬ ℂ→C· k1 ≡ ℂ→C· (Res.def r)
                        → onlyℂ∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → equalInType i w (#Σchoice c k1) x y
                        → ⊥
¬equalInType-#Σchoice i w r c x y {k1} isv₁ isv₂ diff oc comp fb eqi = diff cn₅
  where
    h0 : equalInType i w (#SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k1) #[0]Typeℂ₀₁)) x y
    h0 rewrite #Σchoice≡ c k1 = eqi

    h1 : inbar w (λ w' _ → SUMeq (equalInType i w' #NAT) (λ a b ea → equalInType i w' (#EQ (#APPLY (#CS c) a) (ℂ→C· k1) Typeℂ₀₁·)) w' x y)
    h1 = Bar.∀𝕎-inBarFunc barI aw (equalInType-SUM→ {i} {w} {#NAT} {#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k1) #[0]Typeℂ₀₁} h0)
      where
        aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType i w' #NAT)
                                     (λ a b ea → equalInType i w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k1) #[0]Typeℂ₀₁)))
                                     w' x y
                           → SUMeq (equalInType i w' #NAT)
                                    (λ a b ea → equalInType i w' (#EQ (#APPLY (#CS c) a) (ℂ→C· k1) Typeℂ₀₁·))
                                    w' x y)
        aw w' e' (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) rewrite sub0-#Σchoice-body≡ a₁ c k1 = a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb

    -- 1st jump to bar
    w1 : 𝕎·
    w1 = fst (ChoiceBar.followChoice CB c h1 oc comp fb)

    e1 : w ⊑· w1
    e1 = fst (snd (ChoiceBar.followChoice CB c h1 oc comp fb))

    oc1 : onlyℂ∈𝕎 (Res.def r) c w1
    oc1 = fst (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb)))

    comp1 : compatible· c w1 r
    comp1 = fst (snd (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb))))

    fb1 : freezable· c w1
    fb1 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb)))))

    h2 : SUMeq (equalInType i w1 #NAT) (λ a b ea → equalInType i w1 (#EQ (#APPLY (#CS c) a) (ℂ→C· k1) Typeℂ₀₁·)) w1 x y
    h2 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c h1 oc comp fb)))))

    a₁ : CTerm
    a₁ = fst h2

    a₂ : CTerm
    a₂ = fst (snd h2)

    b₁ : CTerm
    b₁ = fst (snd (snd h2))

    b₂ : CTerm
    b₂ = fst (snd (snd (snd h2)))

    ea1 : equalInType i w1 #NAT a₁ a₂
    ea1 = fst (snd (snd (snd (snd h2))))

    eb1 : equalInType i w1 (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k1) Typeℂ₀₁·) b₁ b₂
    eb1 = snd (snd (snd (snd (snd (snd (snd h2))))))

    -- 2nd jump to bar
    ea2 : inbar w1 (λ w' _ → #strongMonEq w' a₁ a₂)
    ea2 = equalInType-NAT→ i w1 a₁ a₂ ea1

    w2 : 𝕎·
    w2 = fst (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1))

    oc2 : onlyℂ∈𝕎 (Res.def r) c w2
    oc2 = fst (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)))

    comp2 : compatible· c w2 r
    comp2 = fst (snd (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1))))

    fb2 : freezable· c w2
    fb2 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)))))

    ea3 : #strongMonEq w2 a₁ a₂
    ea3 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c ea2 oc1 comp1 fb1)))))

    m : ℕ
    m = fst ea3

    ca₁ : a₁ #⇛ #NUM m at w2
    ca₁ = fst (snd ea3)

    eb2 : equalInType i w2 (#EQ (#APPLY (#CS c) a₁) (ℂ→C· k1) Typeℂ₀₁·) b₁ b₂
    eb2 = equalInType-mon eb1 w2 e2

    eb3 : equalInType i w2 Typeℂ₀₁· (#APPLY (#CS c) a₁) (ℂ→C· k1)
    eb3 = equalInType-EQ→₁ eb2

    eb4 : equalInType i w2 Typeℂ₀₁· (#APPLY (#CS c) (#NUM m)) (ℂ→C· k1)
    eb4 = equalInType-#⇛-left (#⇛-APPLY-CS {w2} {a₁} {#NUM m} c ca₁) eb3

    eb5 : inbar w2 (λ w' _ → #weakℂEq w' (#APPLY (#CS c) (#NUM m)) (ℂ→C· k1))
    eb5 = ∈Typeℂ₀₁→· i w2 (#APPLY (#CS c) (#NUM m)) (ℂ→C· k1) eb4

    -- 3rd jump to bar
    w3 : 𝕎·
    w3 = fst (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)

    e3 : w2 ⊑· w3
    e3 = fst (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2))

    oc3 : onlyℂ∈𝕎 (Res.def r) c w3
    oc3 = fst (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)))

    comp3 : compatible· c w3 r
    comp3 = fst (snd (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2))))

    fb3 : freezable· c w3
    fb3 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)))))

    eb6 : #weakℂEq w3 (#APPLY (#CS c) (#NUM m)) (ℂ→C· k1)
    eb6 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c eb5 oc2 comp2 fb2)))))

    gc : inbar w3 (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t))))
    gc = inbar-choice· w3 c m r comp3

    -- 4th jump to bar
    w4 : 𝕎·
    w4 = fst (ChoiceBar.followChoice CB c gc oc3 comp3 fb3)

    e4 : w3 ⊑· w4
    e4 = fst (snd (ChoiceBar.followChoice CB c gc oc3 comp3 fb3))

    oc4 : onlyℂ∈𝕎 (Res.def r) c w4
    oc4 = fst (snd (snd (ChoiceBar.followChoice CB c gc oc3 comp3 fb3)))

    comp4 : compatible· c w4 r
    comp4 = fst (snd (snd (snd (ChoiceBar.followChoice CB c gc oc3 comp3 fb3))))

    fb4 : freezable· c w4
    fb4 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c gc oc3 comp3 fb3)))))

    gc1 : ∀𝕎 w4 (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ ℂ· (λ t → getChoice· m c w' ≡ just t)))
    gc1 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c gc oc3 comp3 fb3)))))

    eb7 : #weakℂEq w4 (#APPLY (#CS c) (#NUM m)) (ℂ→C· k1)
    eb7 = ∀𝕎-mon e4 eb6

    -- and now we conclude
    k : ℂ·
    k = fst (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7)

    cn₁ : #APPLY (#CS c) (#NUM m) #⇓ ℂ→C· k at w4
    cn₁ = fst (snd (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7))

    cn₂ : ℂ→C· k1 #⇓ ℂ→C· k at w4
    cn₂ = snd (snd (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7))

    gc2 : Σ ℂ· (λ t → getChoice· m c w4 ≡ just t)
    gc2 = lower (gc1 w4 (⊑-refl· _))

    cn₃ : ℂ→C· k #⇓ ℂ→C· (Res.def r) at w4
    cn₃ = onlyℂ∈𝕎→≡ oc4 cn₁ gc2 isv₁

    cn₄ : ℂ→C· k1 #⇓ ℂ→C· (Res.def r) at w4
    cn₄ = ⇓-trans cn₂ cn₃

    cn₅ : ℂ→C· k1 ≡ ℂ→C· (Res.def r)
    cn₅ = CTerm≡ (compVal (ℂ→T k1) (ℂ→T (Res.def r)) w4 cn₄ isv₂)

{--
    neq1 : ℂ→T (Res.def r) ⇓ NUM k at w3
    neq1 = onlyℂ∈𝕎→≡ oc3 (lower (ca₁ w3 e3)) cn₁ tt {--isvd--}

    neq2 : k1 ≡ k
    neq2 = NUMinj (compVal (NUM k1) (NUM k) w3 cn₂ tt)

    neq3 : ℂ→T (Res.def r) ⇓ NUM k1 at w3
    neq3 = ≡→⇓→⇓ (≡NUM (sym neq2)) neq1 -- rewrite sym neq2 = neq1
--}


{--¬-ℕ→ℂ→T-⇓-NUM-1 : (w : 𝕎·) → ¬ ℂ→T (ℕ→ℂ· 0) ⇓ NUM 1 at w
¬-ℕ→ℂ→T-⇓-NUM-1 w h rewrite ℕ→ℂ→T· 0 = ¬≡s 0 (NUMinj (compVal (NUM 0) (NUM 1) w h tt))
--}



{--
-- If we don't use this Agda gets stuck compiling...
∀𝕎-getChoice→getC : {w : 𝕎·} {n : ℕ} {name : Name} {k : ℕ}
                      → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getChoice· n name w' ≡ just (ℕ→ℂ· k)))
                      → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getC n name w' ≡ just (NUM k)))
∀𝕎-getChoice→getC {w} {n} {name} {k} aw w' e' rewrite lower (aw w' e') | ℕ→ℂ→T· k = lift refl
--}


--}


-- use equalInType-FUN instead
¬LPO : (w : 𝕎·) → member w (#NEG #LPO) #lamAX
¬LPO w = n , equalInType-NEG (λ w1 e1 → isTypeLPO w1 n) aw1
  where
    n : ℕ
    n = 1

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #LPO a₁ a₂)
    aw1 w1 e1 a₁ a₂ ea = {!!} --concl h5
      where

{--        aw1' : equalInType n w1 (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))) a₁ a₂
        aw1' rewrite #LEM≡#PI p = ea

        aw2 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → equalInType n w' (#SQUASH (#UNION (#↑T p u₁) (#NEG (#↑T p u₁)))) (#APPLY a₁ u₁) (#APPLY a₂ u₂))
        aw2 w' e' u₁ u₂ j = ≡CTerm→equalInType (sub0-#[0]SQUASH p u₁) (snd (snd (equalInType-PI→ aw1')) w' e' u₁ u₂ j)

        aw3 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → inbar w' (λ w'' _ → Σ CTerm (λ t → equalInType n w'' (#UNION (#↑T p u₁) (#NEG (#↑T p u₁))) t t)))
        aw3 w' e' u₁ u₂ j = equalInType-SQUASH→ (aw2 w' e' u₁ u₂ j)

        aw4 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → inbar w' (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType n w' (#↑T p u₁) x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × equalInType n w' (#NEG (#↑T p u₁)) x y)))))))
        aw4 w' e' u₁ u₂ j = Bar.∀𝕎-inBarFunc barI aw' (aw3 w' e' u₁ u₂ j)
          where
            aw' : ∀𝕎 w' (λ w'' _ → Σ CTerm (λ t → equalInType n w'' (#UNION (#↑T p u₁) (#NEG (#↑T p u₁))) t t)
                                  → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType n w' (#↑T p u₁) x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × equalInType n w' (#NEG (#↑T p u₁)) x y))))))
            aw' w'' e'' (t , eqi) = t , equalInType-UNION→ eqi

        aw5 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → inbar w' (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' u₁ x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w'
                                                      × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' u₁ a₁ a₂))))))))
        aw5 w' e' u₁ u₂ j = Bar.∀𝕎-inBarFunc barI aw' (aw4 w' e' u₁ u₂ j)
          where
            aw' : ∀𝕎 w' (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType n w' (#↑T p u₁) x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × equalInType n w' (#NEG (#↑T p u₁)) x y)))))
                                  → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' u₁ x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' u₁ a₁ a₂)))))))
            aw' w'' e'' (t , eqt) = t , Bar.∀𝕎-inBarFunc barI (λ { w3 e3 (x , y , inj₁ (c₁ , c₂ , z)) → x , y , inj₁ (c₁ , c₂ , equalInType-#↑T→ p w3 u₁ x y z) ;
                                                                    w3 e3 (x , y , inj₂ (c₁ , c₂ , z)) → x , y , inj₂ (c₁ , c₂ , equalInType-NEG-↑T→ p z) })
                                                               eqt

        -- instantiate using #Σchoice
        name : Name
        name = newChoice· w1

        r : Res
        r = Resℂ

        w2 : 𝕎·
        w2 = startChoice· name r w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏· r w1

        k1 : ℂ·
        k1 = ℂ₁· -- This has to be different from r's default value

        dks : ¬ ℂ→C· k1 ≡ ℂ→C· (Res.def r)
        dks = λ x → ℂ₀≠ℂ₁· (sym x)

        -- instantiate aw5 with w2 (we also need a proof that (w1 ⊑ w2)) and (#Σchoice name k1)
        h1 : inbar w2 (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                               → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' (#Σchoice name k1) x y)
                                  ⊎
                                  (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w'
                                   × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂)))))))
        h1 = aw5 w2 e2 (#Σchoice name k1) (#Σchoice name k1) (equalInType-#Σchoice p w2 name k1 (startChoiceCompatible· r w1) Σsat-ℂ₁)

        oc1 : onlyℂ∈𝕎 (Res.def r) name w2
        oc1 n = getChoice-startNewChoice· n r w1 --rewrite getChoice-startNewChoice· n r w1 = ⊥-elim (¬just≡nothing (sym e))

        comp1 : compatible· name w2 r
        comp1 = startChoiceCompatible· r w1

        fb1 : freezable· name w2
        fb1 = freezableStart· r w1

        h2 : Σ 𝕎· (λ w3 → Σ (w2 ⊑· w3) (λ e3 → onlyℂ∈𝕎 (Res.def r) name w3 × compatible· name w3 Resℂ × freezable· name w3 ×
             Σ CTerm (λ t → inbar w3 (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                              → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' (#Σchoice name k1) x y)
                                                 ⊎
                                                 (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w'
                                                  × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂))))))))
        h2 = ChoiceBar.followChoice CB name h1 oc1 comp1 fb1

        w3 : 𝕎·
        w3 = fst h2

        e3 : w2 ⊑· w3
        e3 = fst (snd h2)

        oc2 : onlyℂ∈𝕎 (Res.def r) name w3
        oc2 = fst (snd (snd h2))

        comp2 : compatible· name w3 r
        comp2 = fst (snd (snd (snd h2)))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd h2))))

        t : CTerm
        t = fst (snd (snd (snd (snd (snd h2)))))

        h3 : inbar w3 (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                              → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' (#Σchoice name k1) x y)
                                 ⊎
                                 (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w'
                                  × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂)))))
        h3 = snd (snd (snd (snd (snd (snd h2)))))

        h4 : Σ 𝕎· (λ w4 → Σ (w3 ⊑· w4) (λ e4 → onlyℂ∈𝕎 (Res.def r) name w4 × compatible· name w4 r × freezable· name w4 ×
                         Σ CTerm (λ x → Σ CTerm (λ y
                         → (t #⇛ (#INL x) at w4 × t #⇛ (#INL y) at w4 × equalInType i w4 (#Σchoice name k1) x y)
                            ⊎
                            (t #⇛ (#INR x) at w4 × t #⇛ (#INR y) at w4
                             × ∀𝕎 w4 (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂))))))
        h4 = ChoiceBar.followChoice CB name h3 oc2 comp2 fb2

        w4 : 𝕎·
        w4 = fst h4

        e4 : w3 ⊑· w4
        e4 = fst (snd h4)

        oc3 : onlyℂ∈𝕎 (Res.def r) name w4
        oc3 = fst (snd (snd h4))

        comp3 : compatible· name w4 r
        comp3 = fst (snd (snd (snd h4)))

        fb3 : freezable· name w4
        fb3 = fst (snd (snd (snd (snd h4))))

        x : CTerm
        x = fst (snd (snd (snd (snd (snd h4)))))

        y : CTerm
        y = fst (snd (snd (snd (snd (snd (snd h4))))))

        h5 : (t #⇛ (#INL x) at w4 × t #⇛ (#INL y) at w4 × equalInType i w4 (#Σchoice name k1) x y)
             ⊎
             (t #⇛ (#INR x) at w4 × t #⇛ (#INR y) at w4
              × ∀𝕎 w4 (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂))
        h5 = snd (snd (snd (snd (snd (snd (snd h4))))))

        -- 1st injection: proved by ¬equalInType-#Σchoice
        -- For this it is enough to be able to make a choice different from k1 forever, for example choosing 0 forever

        -- 2nd injection:
        -- This is where we should be able to make another choice than the default choice
        w5 : 𝕎·
        w5 = freeze· name w4 k1

        rNUM : ⋆ᵣ r k1
        rNUM = sat-ℂ₁

        e5 : w4 ⊑· w5
        e5 = freeze⊑· name w4 k1 comp3 rNUM

        n1 : ℕ
        n1 = fst (getFreeze· name w4 k1 comp3 fb3)

        g0 : ∀𝕎 w5 (λ w' _ → Lift (lsuc(L)) (getChoice· n1 name w' ≡ just k1))
        g0 = snd (getFreeze· name w4 k1 comp3 fb3)

        g1 : #APPLY (#CS name) (#NUM n1) #⇛ ℂ→C· k1 at w5 -- ∀𝕎 w5 (λ w' _ → Lift (lsuc(L)) (getC n1 name w' ≡ just (NUM k1)))
        g1 = →#APPLY-#CS#⇛ℂ→C· g0 --∀𝕎-getChoice→getC g0

        h6 : equalInType i w5 (#Σchoice name k1) (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX)
        h6 = getChoice→equalInType-#Σchoice i (⊑-compatible· e5 comp3) (sat-ℂ₁ 0) g1 --getChoice→equalInType-#Σchoice i (⊑-compatible· e5 comp3) g1

        e' : w ⊑· w4
        e' = ⊑-trans· (⊑-trans· (⊑-trans· e1 e2) e3) e4

        -- conclusion
        concl : ((t #⇛ (#INL x) at w4 × t #⇛ (#INL y) at w4 × equalInType i w4 (#Σchoice name k1) x y)
                 ⊎
                 (t #⇛ (#INR x) at w4 × t #⇛ (#INR y) at w4
                  × ∀𝕎 w4 (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂)))
                → ⊥
        concl (inj₁ (c₁ , c₂ , eqi)) = ¬equalInType-#Σchoice i w4 Resℂ name x y isValueℂ₀· isValueℂ₁· dks oc3 comp3 fb3 eqi
        concl (inj₂ (c₁ , c₂ , aw)) = aw w5 e5 (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX) h6
--}

\end{code}[hide]
