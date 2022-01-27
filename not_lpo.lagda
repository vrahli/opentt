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
open import compatible
open import progress
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar


module not_lpo {L : Level} (W : PossibleWorlds {L})
               (C : Choice) (M : Compatible W C) (P : Progress {L} W C M)
               (G : GetChoice {L} W C M) (X : ChoiceExt {L} C) (N : NewChoice {L} W C M G)
               (F : Freeze {L} W C M P G N)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
               (CB : ChoiceBar W C M P G X N F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import newChoiceDef(W)(C)(M)(G)(N)
open import choiceExtDef(W)(C)(M)(G)(X)
open import freezeDef(W)(C)(M)(P)(G)(N)(F)
open import computation(W)(C)(M)(G)
open import bar(W)
open import barI(W)(C)(M)(P)
open import theory(W)(C)(M)(P)(G)(E)
open import props0(W)(C)(M)(P)(G)(E)
open import ind2(W)(C)(M)(P)(G)(E)

open import props1(W)(C)(M)(P)(G)(E)
open import props2(W)(C)(M)(P)(G)(E)
open import props3(W)(C)(M)(P)(G)(E)
open import lem_props(W)(C)(M)(P)(G)(X)(E)

open import not_lem(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)

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


-- If we only want to consider Boolean choices
Boolℂ : ChoiceBar W C M P G X N F E → Set
Boolℂ cb = ChoiceBar.Typeℂ₀₁ cb ≡ #BOOL


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



-- TODO: generalize
→equalInType-CS-NAT→BOOL : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #BOOL (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT→BOOL (#CS a) (#CS b)
→equalInType-CS-NAT→BOOL {n} {w} {a} {b} i rewrite #NAT→BOOL≡ =
  equalInType-FUN (λ w' _ → eqTypesNAT) (λ w' _ → isTypeBOOL w' n) aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT a₁ a₂
                      → equalInType n w' #BOOL (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
    aw w1 e1 a₁ a₂ ea = equalInType-local (Bar.∀𝕎-inBarFunc barI aw1 ea1)
      where
        ea1 : inbar w1 (λ w' _ → #strongMonEq w' a₁ a₂)
        ea1 = equalInType-NAT→ n w1 a₁ a₂ ea

        aw1 : ∀𝕎 w1 (λ w' e' → #strongMonEq w' a₁ a₂ → equalInType n w' #BOOL (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
        aw1 w2 e2 (m , c₁ , c₂) = equalInType-#⇛-LR-rev (#⇛-APPLY-CS {w2} {a₁} {#NUM m} a c₁)
                                                         (#⇛-APPLY-CS {w2} {a₂} {#NUM m} b c₂)
                                                         (i w2 (⊑-trans· e1 e2) m)



-- MOVE to props3
fun-equalInType-SQUASH-UNION : {n : ℕ} {w : 𝕎·} {a b c d u v : CTerm}
                               → isType n w c
                               → isType n w d
                               → ∀𝕎 w (λ w' _ → inhType n w' a → inhType n w' c)
                               → ∀𝕎 w (λ w' _ → inhType n w' b → inhType n w' d)
                               → equalInType n w (#SQUASH (#UNION a b)) u v
                               → equalInType n w (#SQUASH (#UNION c d)) #AX #AX
fun-equalInType-SQUASH-UNION {n} {w} {a} {b} {c} {d} {u} {v} istc istd imp1 imp2 eqi =
  →equalInType-SQUASH (Bar.∀𝕎-inBar barI (λ w' _ → #compAllRefl #AX w'))
                       (Bar.∀𝕎-inBar barI (λ w' _ → #compAllRefl #AX w'))
                       (Bar.inBar-idem barI (Bar.∀𝕎-inBarFunc barI aw1 (equalInType-SQUASH→ eqi)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType n w' (#UNION a b) → inbar w' (λ w'' e'' → (z : w ⊑· w'') → inhType n w'' (#UNION c d)))
    aw1 w1 e1 (t , eqj) = Bar.∀𝕎-inBarFunc barI aw2 (equalInType-UNION→ eqj)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                                      (t #⇛ #INL x at w' × t #⇛ #INL y at w' × equalInType n w' a x y)
                                      ⊎ (t #⇛ #INR x at w' × t #⇛ #INR y at w' × equalInType n w' b x y)))
                            → (z : w ⊑· w') → inhType n w' (#UNION c d))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , eqk)) z = #INL (fst (imp1 w2 z (x , equalInType-refl eqk))) , eql
          where
            eql : ∈Type n w2 (#UNION c d) (#INL (fst (imp1 w2 z (x , equalInType-refl eqk))))
            eql = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Bar.∀𝕎-inBar barI λ w3 e3 → fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                                     fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                                     inj₁ (#compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           #compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           equalInType-mon (snd (imp1 w2 z (x , equalInType-refl eqk))) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , eqk)) z = #INR (fst (imp2 w2 z (x , equalInType-refl eqk))) , eqr
          where
            eqr : ∈Type n w2 (#UNION c d) (#INR (fst (imp2 w2 z (x , equalInType-refl eqk))))
            eqr = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Bar.∀𝕎-inBar barI λ w3 e3 → fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                                     fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                                     inj₂ (#compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           #compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           equalInType-mon (snd (imp2 w2 z (x , equalInType-refl eqk))) w3 e3))



-- Assuming that our choices are Bools
¬LPO : Boolℂ CB → (w : 𝕎·) → member w (#NEG #LPO) #lamAX
¬LPO bcb w = n , equalInType-NEG (λ w1 e1 → isTypeLPO w1 n) aw1
  where
    n : ℕ
    n = 1

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #LPO a₁ a₂)
    aw1 w1 e1 F G ea =
      h (fun-equalInType-SQUASH-UNION (equalInType-#Σchoice w2 name ℂ₁· comp1 (0 , sat-ℂ₁ 0))
                                      (eqTypesNEG← (equalInType-#Σchoice w2 name ℂ₁· comp1 (0 , sat-ℂ₁ 0)))
                                      imp1
                                      imp2
                                      h2)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT→BOOL f g
                             → equalInType n w' (sub0 f (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT→BOOL} {#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right)} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT→BOOL f g
                             → equalInType n w' (#SQUASH (#UNION (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G g))
        aw3 w' e f g ex = ≡CTerm→equalInType (sub0-squash-union-LPO f) (aw2 w' e f g ex)

        name : Name
        name = newChoice· w1

        w2 : 𝕎·
        w2 = startNewChoice Resℂ w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏· Resℂ w1

        comp1 : compatible· name w2 Resℂ
        comp1 = startChoiceCompatible· Resℂ w1

        h : ¬ equalInType n w2 (sq-dec (#Σchoice name ℂ₁·)) #AX #AX
        h = ¬-dec-Σchoice w1 n

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType bcb (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT n w' m))

        eqf1 : ∈Type n w2 #NAT→BOOL f
        eqf1 = →equalInType-CS-NAT→BOOL eqf2

        h1 : equalInType n w2 (sub0 f (#[0]SQUASH (#[0]UNION #[0]LPO-left #[0]LPO-right))) (#APPLY F f) (#APPLY G f)
        h1 = aw2 w2 e2 f f eqf1

        h2 : equalInType n w2 (#SQUASH (#UNION (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G f)
        h2 = ≡CTerm→equalInType (sub0-squash-union-LPO f) h1

        imp1 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-left f) → inhType n w' (#Σchoice name ℂ₁·))
        imp1 w3 e3 inh = {!!}

        imp2 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-right f) → inhType n w' (#NEG (#Σchoice name ℂ₁·)))
        imp2 w3 e3 inh = {!!}

\end{code}[hide]
