\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


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
open import name
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import newChoice
open import progress
open import mod
open import encode


module lem_props {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice W C K G)
--                 (V : ChoiceVal W C K G X N)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(K)(G)
--open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)

--open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

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
LEM : {i n : ℕ} (p : i < n) → Term
LEM {i} {n} p = PI (UNIV i) (SQUASH (UNION (↑T p (VAR 0)) (NEG (↑T p (VAR 0)))))


#LEM : {i n : ℕ} (p : i < n) → CTerm
#LEM {i} {n} p = ct (LEM p) c
  where
    c : # LEM p
    c rewrite fvars-↑T p (VAR 0)
            | shiftUp-↑T p 0 (VAR 0)
            | fvars-↑T p (VAR 1) = refl


#LEM≡#PI : {i n : ℕ} (p : i < n) → #LEM p ≡ #PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))
#LEM≡#PI {i} {n} p = CTerm≡ refl


{--equalTerms-NegLem : (w : 𝕎·) {i n : ℕ} (p : i < n) → equalTerms n w (eqTypesNegLem w p) #lamAX #lamAX
equalTerms-NegLem w {i} {n} p =
  {!!}
--}



sub0-#[0]SQUASH-LEM : {i n : ℕ} (p : i < n) (a : CTerm)
                      → sub0 a (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))
                        ≡ #SQUASH (#UNION (#↑T p a) (#NEG (#↑T p a)))
sub0-#[0]SQUASH-LEM {i} {n} p a rewrite sub0-#[0]SQUASH a (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))) =
  CTerm≡ (≡SET refl e)
  where
    e : UNION (shiftUp 0 (shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) (↑T p (VAR 0)))))
              (PI (shiftUp 0 (shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) (↑T p (VAR 0)))))
                  (EQ (NUM 0) (NUM 1) NAT))
        ≡ UNION (shiftUp 0 (↑T p ⌜ a ⌝)) (PI (shiftUp 0 (↑T p ⌜ a ⌝)) (EQ (NUM 0) (NUM 1) NAT))
    e rewrite #shiftUp 0 a | subv-↑T p 0 ⌜ a ⌝ | shiftDown-↑T p 0 ⌜ a ⌝ | #shiftDown 0 a | shiftUp-↑T p 0 ⌜ a ⌝ = refl


-- We need cumulativity or lifting here because (#UNIV i) needs to be in level i,
-- but a₁ needs to be equal to a₂ at that level and also in (#UNIV i)
isTypeLemPi : (w : 𝕎·) {n i : ℕ} (p : i < n)
               → isType n w (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
isTypeLemPi w {n} {i} p =
  eqTypesPI←
    {w} {n}
    {#UNIV i} {#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))}
    {#UNIV i} {#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))}
    (λ w1 e1 → eqTypesUniv w1 n i p)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' (#UNIV i) a₁ a₂)
                       → equalTypes n w'
                                     (sub0 a₁ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                                     (sub0 a₂ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))))
    aw w1 e1 a₁ a₂ ea rewrite sub0-#[0]SQUASH-LEM p a₁ | sub0-#[0]SQUASH-LEM p a₂ = aw'
      where
        aw' : equalTypes n w1 (#SQUASH (#UNION (#↑T p a₁) (#NEG (#↑T p a₁)))) (#SQUASH (#UNION (#↑T p a₂) (#NEG (#↑T p a₂))))
        aw' = eqTypesSQUASH← (eqTypesUNION← (equalInType→equalTypes {n} {i} p w1 a₁ a₂ ea)
                                             (eqTypesNEG← (equalInType→equalTypes {n} {i} p w1 a₁ a₂ ea)))


eqTypesLem : (w : 𝕎·) {n i : ℕ} (p : i < n) → isType n w (#LEM p)
eqTypesLem w {n} {i} p rewrite #LEM≡#PI p = isTypeLemPi w {n} {i} p


eqTypesNegLem : (w : 𝕎·) {n i : ℕ} (p : i < n) → isType n w (#NEG (#LEM p))
eqTypesNegLem w {n} {i} p = eqTypesNEG← (eqTypesLem w {n} {i} p)



{--
#ℂ→T : (c : ℂ·) → CTerm
#ℂ→T c = ct (ℂ→T· c) (#-ℂ→T c)


#[0]ℂ→T : (c : ℂ·) → CTerm0
#[0]ℂ→T c = ⌞ #ℂ→T c ⌟
--}



{--
→inbar-#weakMonEq-APPLY-CS-left : (w : 𝕎·) (a t : CTerm) (m : ℕ) (c : Name)
                                   → a #⇛ #NUM m at w
                                   → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) t)
                                   → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) a) t)
→inbar-#weakMonEq-APPLY-CS-left w a t m c c₁ i = Bar.∀𝕎-inBarFunc barI aw i
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) t
                        → #weakMonEq w' (#APPLY (#CS c) a) t)
    aw w' e' h w'' e'' = lift (fst z ,
                               ⇓-trans (⇓-APPLY-CS w'' ⌜ a ⌝ (NUM m) c d₁) (fst (snd z)) ,
                               snd (snd z))
      where
        z : Σ ℕ (λ n → (APPLY (CS c) (NUM m)) ⇓ (NUM n) at w'' × ⌜ t ⌝ ⇓ (NUM n) at w'')
        z = lower (h w'' e'')

        d₁ : ⌜ a ⌝ ⇓ NUM m at w''
        d₁ = lower (c₁ w'' (⊑-trans· e' e''))
--}



{--
→inbar-#weakMonEq-APPLY-CS-left-rev : (w : 𝕎·) (a t : CTerm) (m : ℕ) (c : Name)
                                       → a #⇛ #NUM m at w
                                       → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) a) t)
                                       → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) t)
→inbar-#weakMonEq-APPLY-CS-left-rev w a t m c c₁ i = Bar.∀𝕎-inBarFunc barI aw i
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq w' (#APPLY (#CS c) a) t
                        → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) t)
    aw w' e' h w'' e'' = lift (fst z , {!!} , snd (snd z))
      where
        z : Σ ℕ (λ n → (APPLY (CS c) ⌜ a ⌝) ⇓ (NUM n) at w'' × ⌜ t ⌝ ⇓ (NUM n) at w'')
        z = lower (h w'' e'')
--}


{--
-- TODO: use →inbar-#weakMonEq-APPLY-CS-left instead
→inbar-#weakMonEq-APPLY-CS : (w : 𝕎·) (a₁ a₂ : CTerm) (m : ℕ) (c : Name)
                              → a₁ #⇛ #NUM m at w
                              → a₂ #⇛ #NUM m at w
                              → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) (#APPLY (#CS c) (#NUM m)))
                              → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂))
→inbar-#weakMonEq-APPLY-CS w a₁ a₂ m c c₁ c₂ i = Bar.∀𝕎-inBarFunc barI aw i
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) (#APPLY (#CS c) (#NUM m))
                        → #weakMonEq w' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂))
    aw w' e' h w'' e'' = lift (fst z ,
                               ⇓-trans (⇓-APPLY-CS w'' ⌜ a₁ ⌝ (NUM m) c d₁) (fst (snd z)) ,
                               ⇓-trans (⇓-APPLY-CS w'' ⌜ a₂ ⌝ (NUM m) c d₂) (fst (snd z)))
      where
        z : Σ ℕ (λ n → (APPLY (CS c) (NUM m)) ⇓ (NUM n) at w'' × (APPLY (CS c) (NUM m)) ⇓ (NUM n) at w'')
        z = lower (h w'' e'')

        d₁ : ⌜ a₁ ⌝ ⇓ NUM m at w''
        d₁ = lower (c₁ w'' (⊑-trans· e' e''))

        d₂ : ⌜ a₂ ⌝ ⇓ NUM m at w''
        d₂ = lower (c₂ w'' (⊑-trans· e' e''))
--}


{--
inbar-#weakMonEq-APPLY-CS : (u : ℕ) (w : 𝕎·) (c : Name) (m : ℂ·)
                            → compatible· c w Resℂ
                            → ∈Type u w Typeℂ₀₁· (#APPLY (#CS c) (ℂ→C· m))
inbar-#weakMonEq-APPLY-CS u w c m comp =
  {!!}
{-- Bar.∀𝕎-inBarFunc barI aw (ChoiceBar.choice-weakℕ CB m comp)
  where
    aw : ∀𝕎 w (λ w' e' → weakℕM w' (getC m c)
                        → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) (#APPLY (#CS c) (#NUM m)))
    aw w' e' h w'' e'' = lift (fst (snd (snd (lower (h w'' e'')))) ,
                               step-⇓-trans (fst (snd (lower (h w'' e'')))) (snd (snd (snd (lower (h w'' e''))))) ,
                               step-⇓-trans (fst (snd (lower (h w'' e'')))) (snd (snd (snd (lower (h w'' e''))))))
--}
--}





onlyℂ∈𝕎→≡-aux : {w : 𝕎·} {c : Name} {v : Term} {u : ℂ·} {k m : ℕ}
                  → onlyℂ∈𝕎 u c w
                  → steps k (APPLY (CS c) (NUM m) , w) ≡ (v , w)
                  → Σ ℂ· (λ t → getChoice· m c w ≡ just t)
                  → isValue (ℂ→T u)
--                         → isValue u
                  → v ⇓! ℂ→T u at w
onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {0} {m} oc c₁ (t , gc) isv {--isu--} rewrite sym (pair-inj₁ c₁) | sym (pair-inj₂ c₁) = 1 , z
  where
    z : steps 1 (APPLY (CS c) (NUM m) , w) ≡ (ℂ→T u , w)
    z rewrite gc | oc m t gc = refl
onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {suc k} {m} oc c₁ gc isv {--isu--}  with getChoice⊎ m c w
... | inj₁ (z , p) rewrite p | oc m z p | stepsVal (ℂ→T u) w k isv | c₁ = 0 , refl
... | inj₂ p rewrite p | sym c₁ = ⊥-elim (¬just≡nothing (sym (snd gc)))



onlyℂ∈𝕎→≡ : {w : 𝕎·} {c : Name} {v : Term} {u : ℂ·} {m : ℕ}
              → onlyℂ∈𝕎 u c w
              → APPLY (CS c) (NUM m) ⇓! v at w
              → Σ ℂ· (λ t → getChoice· m c w ≡ just t)
              → isValue (ℂ→T u)
              → v ⇓! ℂ→T u at w
onlyℂ∈𝕎→≡ {w} {c} {v} {u} {m} oc c₁ gc isv {--isu--} =
  onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {k} {m} oc c₂ gc isv {--isu--}
  where
    k : ℕ
    k = fst c₁

    c₂ : steps k (APPLY (CS c) (NUM m) , w) ≡ (v , w)
    c₂ = snd c₁


onlyℂ∈𝕎→⇓ : {w : 𝕎·} {c : Name} {u : ℂ·} {m : ℕ}
              → onlyℂ∈𝕎 u c w
              → Σ ℂ· (λ t → getChoice· m c w ≡ just t)
              → APPLY (CS c) (NUM m) ⇓! ℂ→T u at w
onlyℂ∈𝕎→⇓ {w} {c} {u} {m} oc (t , gc) = 1 , comp
  where
    comp : steps 1 (APPLY (CS c) (NUM m) , w) ≡ (ℂ→T u , w)
    comp rewrite gc | oc m t gc = refl



-- Without that it runs forever...
≡→⇓→⇓ : {w : 𝕎·} {a b c : Term}
         → b ≡ c
         → a ⇓ b at w
         → a ⇓ c at w
≡→⇓→⇓ {w} {a} {b} {c} h q rewrite h = q


≡NUM : {a b : ℕ} → a ≡ b → NUM a ≡ NUM b
≡NUM {a} {b} e rewrite e = refl


→#APPLY-#CS#⇛ℂ→C· : {w : 𝕎·} {name : Name} {n : ℕ} {k : ℂ·}
                       → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getChoice· n name w' ≡ just k))
                       → #APPLY (#CS name) (#NUM n) #⇛! ℂ→C· k at w
→#APPLY-#CS#⇛ℂ→C· {w} {name} {n} {k} aw w1 e1 = lift (1 , step-APPLY-CS (ℂ→T k) w1 n name h)
  where
    h : getT n name w1 ≡ just (ℂ→T k)
    h rewrite lower (aw w1 e1) = refl


QTNAT!→QTBOOL! : Term
QTNAT!→QTBOOL! = FUN QTNAT! QTBOOL!


#QTNAT!→QTBOOL! : CTerm
#QTNAT!→QTBOOL! = ct QTNAT!→QTBOOL! refl


#QTNAT!→QTBOOL!≡ : #QTNAT!→QTBOOL! ≡ #FUN #QTNAT! #QTBOOL!
#QTNAT!→QTBOOL!≡ = CTerm≡ refl


#SUM-ASSERT₂ : CTerm → CTerm
#SUM-ASSERT₂ f = #SUM #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#PI-NEG-ASSERT₂ : CTerm → CTerm
#PI-NEG-ASSERT₂ f = #PI #NAT! (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))


#SUM-ASSERT₃ : CTerm → CTerm
#SUM-ASSERT₃ f = #SUM #NAT! (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#PI-NEG-ASSERT₃ : CTerm → CTerm
#PI-NEG-ASSERT₃ f = #PI #NAT! (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))


#SUM-ASSERT₄ : CTerm → CTerm
#SUM-ASSERT₄ f = #SUM #QTNAT! (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


ASSERT₄ : Term → Term
ASSERT₄ t = EQ t BTRUE BOOL₀!


fvars-ASSERT₄ : (t : Term) → fvars (ASSERT₄ t) ≡ fvars t
fvars-ASSERT₄ t rewrite ++[] (fvars t) = refl


#ASSERT₄ : CTerm → CTerm
#ASSERT₄ a = ct (ASSERT₄ ⌜ a ⌝) c
  where
    c : # ASSERT₄ ⌜ a ⌝
    c rewrite fvars-ASSERT₄ ⌜ a ⌝ = CTerm.closed a


#ASSERT₄≡ : (t : CTerm) → #ASSERT₄ t ≡ #EQ t #BTRUE #BOOL₀!
#ASSERT₄≡ t = CTerm≡ refl


#[0]ASSERT₄ : CTerm0 → CTerm0
#[0]ASSERT₄ a = ct0 (ASSERT₄ ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ASSERT₄ ⌜ a ⌝
    c rewrite fvars-ASSERT₄ ⌜ a ⌝ = CTerm0.closed a


#[1]ASSERT₄ : CTerm1 → CTerm1
#[1]ASSERT₄ a = ct1 (ASSERT₄ ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] ASSERT₄ ⌜ a ⌝
    c rewrite fvars-ASSERT₄ ⌜ a ⌝ = CTerm1.closed a


≡ASSERT₄ : {a b : Term} → a ≡ b → ASSERT₄ a ≡ ASSERT₄ b
≡ASSERT₄ {a} {b} e rewrite e = refl


#SUM-ASSERT₅ : CTerm → CTerm
#SUM-ASSERT₅ f = #SUM #NAT! (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


→equalTypes-#SUM-ASSERT₂ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT!→BOOL₀ a₁ a₂
                           → equalTypes n w (#SUM-ASSERT₂ a₁) (#SUM-ASSERT₂ a₂)
→equalTypes-#SUM-ASSERT₂ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #BOOL₀ (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₂-APPLY a a₁ | sub0-ASSERT₂-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL₀ (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₂ (#APPLY a₁ a)) (#ASSERT₂ (#APPLY a₂ b))
        aw2 = equalInType-BOOL→equalTypes-ASSERT₂ eqb



→equalTypes-#SUM-ASSERT₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT!→QTBOOL! a₁ a₂
                           → equalTypes n w (#SUM-ASSERT₃ a₁) (#SUM-ASSERT₃ a₂)
→equalTypes-#SUM-ASSERT₃ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #NAT!→QTBOOL!≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₃-APPLY a a₁ | sub0-ASSERT₃-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₃ (#APPLY a₁ a)) (#ASSERT₃ (#APPLY a₂ b))
        aw2 = equalInType-QTBOOL!→equalTypes-ASSERT₃ eqb


→equalTypes-#SUM-ASSERT₄ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #QTNAT!→QTBOOL! a₁ a₂
                           → equalTypes n w (#SUM-ASSERT₄ a₁) (#SUM-ASSERT₄ a₂)
→equalTypes-#SUM-ASSERT₄ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → eqTypesQTNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #QTNAT! a b → equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #QTNAT!→QTBOOL!≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #QTNAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₃-APPLY a a₁ | sub0-ASSERT₃-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₃ (#APPLY a₁ a)) (#ASSERT₃ (#APPLY a₂ b))
        aw2 = equalInType-QTBOOL!→equalTypes-ASSERT₃ eqb


sub0-ASSERT₄-APPLY : (a b : CTerm) → sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ b ⌟ #[0]VAR)) ≡ #ASSERT₄ (#APPLY b a)
sub0-ASSERT₄-APPLY a b = CTerm≡ (≡ASSERT₄ (→≡APPLY x y))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl


equalInType-BOOL!→equalTypes-ASSERT₄ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL₀! a b
                                      → equalTypes n w (#ASSERT₄ a) (#ASSERT₄ b)
equalInType-BOOL!→equalTypes-ASSERT₄ {n} {w} {a} {b} eqb =
  ≡CTerm→eqTypes
    (sym (#ASSERT₄≡ a))
    (sym (#ASSERT₄≡ b))
    (eqTypesEQ← (isTypeBOOL₀!→ n w) eqb (→equalInType-BOOL₀!-INL n w #AX #AX))


equalInType-BOOL₀!→equalTypes-ASSERT₄ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL₀! a b
                                      → equalTypes n w (#ASSERT₄ a) (#ASSERT₄ b)
equalInType-BOOL₀!→equalTypes-ASSERT₄ {n} {w} {a} {b} eqb =
  ≡CTerm→eqTypes
    (sym (#ASSERT₄≡ a))
    (sym (#ASSERT₄≡ b))
    (eqTypesEQ← (isTypeBOOL₀!→ n w) eqb (→equalInType-BOOL₀!-INL n w #AX #AX))


→equalTypes-#SUM-ASSERT₅ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT!→BOOL₀! a₁ a₂
                           → equalTypes n w (#SUM-ASSERT₅ a₁) (#SUM-ASSERT₅ a₂)
→equalTypes-#SUM-ASSERT₅ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #BOOL₀! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₄-APPLY a a₁ | sub0-ASSERT₄-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL₀! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₄ (#APPLY a₁ a)) (#ASSERT₄ (#APPLY a₂ b))
        aw2 = equalInType-BOOL₀!→equalTypes-ASSERT₄ eqb


→equalTypes-#PI-NEG-ASSERT₂-body : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                                    → equalInType n w #NAT!→BOOL₀ a₁ a₂
                                    → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                         → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                            (sub0 b (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR)))))
→equalTypes-#PI-NEG-ASSERT₂-body {n} {w} {a₁} {a₂} eqt w' e a b ea
  rewrite sub0-NEG-ASSERT₂-APPLY a a₁ | sub0-NEG-ASSERT₂-APPLY b a₂
  = aw2
  where
    eqb : equalInType n w' #BOOL₀ (#APPLY a₁ a) (#APPLY a₂ b)
    eqb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀≡ eqt) w' e a b ea

    aw2 : equalTypes n w' (#NEG (#ASSERT₂ (#APPLY a₁ a))) (#NEG (#ASSERT₂ (#APPLY a₂ b)))
    aw2 = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT₂ eqb)


→equalTypes-#PI-NEG-ASSERT₂-body2 : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                                     → equalInType n w #NAT!→BOOL₀ a₁ a₂
                                     → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                          → equalTypes n w' (#NEG (#ASSERT₂ (#APPLY a₁ a)))
                                                             (#NEG (#ASSERT₂ (#APPLY a₂ b))))
→equalTypes-#PI-NEG-ASSERT₂-body2 {n} {w} {a₁} {a₂} a∈ w1 e1 a b ea =
  ≡CTerm→eqTypes
    (sub0-NEG-ASSERT₂-APPLY a a₁) (sub0-NEG-ASSERT₂-APPLY b a₂)
    (→equalTypes-#PI-NEG-ASSERT₂-body a∈ w1 e1 a b ea)


→equalTypes-#PI-NEG-ASSERT₂ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                              → equalInType n w #NAT!→BOOL₀ a₁ a₂
                              → equalTypes n w (#PI-NEG-ASSERT₂ a₁) (#PI-NEG-ASSERT₂ a₂)
→equalTypes-#PI-NEG-ASSERT₂ {n} {w} {a₁} {a₂} eqt =
  eqTypesPI← (λ w' _ → isTypeNAT!) (→equalTypes-#PI-NEG-ASSERT₂-body {n} {w} {a₁} {a₂} eqt)



→equalTypes-#PI-NEG-ASSERT₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                              → equalInType n w #NAT!→QTBOOL! a₁ a₂
                              → equalTypes n w (#PI-NEG-ASSERT₃ a₁) (#PI-NEG-ASSERT₃ a₂)
→equalTypes-#PI-NEG-ASSERT₃ {n} {w} {a₁} {a₂} eqt =
  eqTypesPI← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #NAT!→QTBOOL!≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                          (sub0 b (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR)))))
    aw1 w' e a b ea rewrite sub0-NEG-ASSERT₃-APPLY a a₁ | sub0-NEG-ASSERT₃-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #QTBOOL! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#NEG (#ASSERT₃ (#APPLY a₁ a))) (#NEG (#ASSERT₃ (#APPLY a₂ b)))
        aw2 = eqTypesNEG← (equalInType-QTBOOL!→equalTypes-ASSERT₃ eqb)

\end{code}
