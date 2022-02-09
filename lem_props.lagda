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

module lem_props {L : Level} (W : PossibleWorlds {L})
                 (C : Choice) (M : Compatible {L} W C) (P : Progress {L} W C M) (G : GetChoice {L} W C M)
                 (X : ChoiceExt W C M G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(M)(G)
open import bar(W)
open import barI(W)(C)(M)(P)
open import forcing(W)(C)(M)(P)(G)(E)
open import props0(W)(C)(M)(P)(G)(E)
open import ind2(W)(C)(M)(P)(G)(E)

open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(X)

open import type_sys_props_nat(W)(C)(M)(P)(G)(E)
open import type_sys_props_qnat(W)(C)(M)(P)(G)(E)
open import type_sys_props_lt(W)(C)(M)(P)(G)(E)
open import type_sys_props_qlt(W)(C)(M)(P)(G)(E)
open import type_sys_props_free(W)(C)(M)(P)(G)(E)
open import type_sys_props_pi(W)(C)(M)(P)(G)(E)
open import type_sys_props_sum(W)(C)(M)(P)(G)(E)
open import type_sys_props_set(W)(C)(M)(P)(G)(E)
open import type_sys_props_eq(W)(C)(M)(P)(G)(E)
open import type_sys_props_union(W)(C)(M)(P)(G)(E)
open import type_sys_props_tsquash(W)(C)(M)(P)(G)(E)
open import type_sys_props_ffdefs(W)(C)(M)(P)(G)(E)
open import type_sys_props_lift(W)(C)(M)(P)(G)(E)

open import props1(W)(C)(M)(P)(G)(E)
open import props2(W)(C)(M)(P)(G)(E)
open import props3(W)(C)(M)(P)(G)(E)

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
                  → steps k (APPLY (CS c) (NUM m)) w ≡ v
                  → Σ ℂ· (λ t → getChoice· m c w ≡ just t)
                  → isValue (ℂ→T u)
--                         → isValue u
                  → v ⇓ ℂ→T u at w
onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {0} {m} oc c₁ (t , gc) isv {--isu--} rewrite sym c₁ = 1 , z
  where
    z : steps 1 (APPLY (CS c) (NUM m)) w ≡ ℂ→T u
    z rewrite gc | oc m t gc = refl
onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {suc k} {m} oc c₁ gc isv {--isu--}  with getChoice⊎ m c w
... | inj₁ (z , p) rewrite p | oc m z p | stepsVal (ℂ→T u) w k isv | c₁ = 0 , refl
... | inj₂ p rewrite p | sym c₁ = ⊥-elim (¬just≡nothing (sym (snd gc)))



onlyℂ∈𝕎→≡ : {w : 𝕎·} {c : Name} {v : Term} {u : ℂ·} {m : ℕ}
              → onlyℂ∈𝕎 u c w
              → APPLY (CS c) (NUM m) ⇓ v at w
              → Σ ℂ· (λ t → getChoice· m c w ≡ just t)
              → isValue (ℂ→T u)
              → v ⇓ ℂ→T u at w
onlyℂ∈𝕎→≡ {w} {c} {v} {u} {m} oc c₁ gc isv {--isu--} =
  onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {k} {m} oc c₂ gc isv {--isu--}
  where
    k : ℕ
    k = fst c₁

    c₂ : steps k (APPLY (CS c) (NUM m)) w ≡ v
    c₂ = snd c₁


onlyℂ∈𝕎→⇓ : {w : 𝕎·} {c : Name} {u : ℂ·} {m : ℕ}
              → onlyℂ∈𝕎 u c w
              → Σ ℂ· (λ t → getChoice· m c w ≡ just t)
              → APPLY (CS c) (NUM m) ⇓ ℂ→T u at w
onlyℂ∈𝕎→⇓ {w} {c} {u} {m} oc (t , gc) = 1 , comp
  where
    comp : steps 1 (APPLY (CS c) (NUM m)) w ≡ ℂ→T u
    comp rewrite gc | oc m t gc = refl



-- Without that it runs forever...
≡→⇓→⇓ : {w : 𝕎·} {a b c : Term}
         → b ≡ c
         → a ⇓ b at w
         → a ⇓ c at w
≡→⇓→⇓ {w} {a} {b} {c} h q rewrite h = q


≡NUM : {a b : ℕ} → a ≡ b → NUM a ≡ NUM b
≡NUM {a} {b} e rewrite e = refl



#weakℂEq→ : {w : 𝕎·} {a b : CTerm}
             → #weakℂEq w a b
             → (c₁ c₂ : ℂ·) → a #⇓ ℂ→C· c₁ at w → b #⇓ ℂ→C· c₂ at w → ∼C w (ℂ→C· c₁) (ℂ→C· c₂)
#weakℂEq→ {w} {a} {B} h = lower (h w (⊑-refl· w))




→#APPLY-#CS#⇛ℂ→C· : {w : 𝕎·} {name : Name} {n : ℕ} {k : ℂ·}
                       → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getChoice· n name w' ≡ just k))
                       → #APPLY (#CS name) (#NUM n) #⇛ ℂ→C· k at w
→#APPLY-#CS#⇛ℂ→C· {w} {name} {n} {k} aw w1 e1 = lift (1 , (step-APPLY-CS (ℂ→T k) w1 n name h))
  where
    h : getT n name w1 ≡ just (ℂ→T k)
    h rewrite lower (aw w1 e1) = refl
\end{code}
