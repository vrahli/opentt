\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module classical (bar : Bar) where

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
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar


--module classical (bar : Bar) where
module classical {L : Level} (W : PossibleWorlds {L})
                 (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
                 (CB : ChoiceBar W C G N F P)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
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



-- We need cumulativity or lifting here because (#UNIV i) needs to be in level i,
-- but a₁ needs to be equal to a₂ at that level and also in (#UNIV i)
eqTypesLemPi : (w : 𝕎·) {n i : ℕ} (p : i < n)
               → equalTypes n w
                             (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                             (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
eqTypesLemPi w {n} {i} p =
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
    aw w1 e1 a₁ a₂ ea rewrite sub0-#[0]SQUASH p a₁ | sub0-#[0]SQUASH p a₂ = aw'
      where
        aw' : equalTypes n w1 (#SQUASH (#UNION (#↑T p a₁) (#NEG (#↑T p a₁)))) (#SQUASH (#UNION (#↑T p a₂) (#NEG (#↑T p a₂))))
        aw' = eqTypesSQUASH← (eqTypesUNION← (equalInType→equalTypes {n} {i} p w1 a₁ a₂ ea)
                                             (eqTypesNEG← (equalInType→equalTypes {n} {i} p w1 a₁ a₂ ea)))


eqTypesLem : (w : 𝕎·) {n i : ℕ} (p : i < n) → equalTypes n w (#LEM p) (#LEM p)
eqTypesLem w {n} {i} p rewrite #LEM≡#PI p = eqTypesLemPi w {n} {i} p


eqTypesNegLem : (w : 𝕎·) {n i : ℕ} (p : i < n) → equalTypes n w (#NEG (#LEM p)) (#NEG (#LEM p))
eqTypesNegLem w {n} {i} p = eqTypesNEG← (eqTypesLem w {n} {i} p)


Σchoice : (n : Name) (k : ℕ) → Term
Σchoice n k = SUM NAT (EQ (APPLY (CS n) (VAR 0)) (NUM k) QNAT)



#Σchoice : (n : Name) (k : ℕ) → CTerm
#Σchoice n k = ct (Σchoice n k) refl


#Σchoice≡ : (n : Name) (k : ℕ) → #Σchoice n k ≡ #SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS n) #[0]VAR) (#[0]NUM k) #[0]QNAT)
#Σchoice≡ n k = refl


sub0-#Σchoice-body≡ : (a : CTerm) (c : Name) (k : ℕ)
                      → sub0 a (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k) #[0]QNAT)
                         ≡ #EQ (#APPLY (#CS c) a) (#NUM k) #QNAT
sub0-#Σchoice-body≡ a c k = CTerm≡ (→≡EQ (→≡APPLY refl (shiftDownUp ⌜ a ⌝ 0)) refl refl)



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



inbar-#weakMonEq-APPLY-CS : (w : 𝕎·) (c : Name) (m : ℕ)
                            → compatible· c w Resℕ
                            → inbar w (λ w' _ → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) (#APPLY (#CS c) (#NUM m)))
inbar-#weakMonEq-APPLY-CS w c m comp = Bar.∀𝕎-inBarFunc barI aw (ChoiceBar.choice-weakℕ CB m comp)
  where
    aw : ∀𝕎 w (λ w' e' → weakℕM w' (getC m c)
                        → #weakMonEq w' (#APPLY (#CS c) (#NUM m)) (#APPLY (#CS c) (#NUM m)))
    aw w' e' h w'' e'' = lift (fst (snd (snd (lower (h w'' e'')))) ,
                               step-⇓-trans (fst (snd (lower (h w'' e'')))) (snd (snd (snd (lower (h w'' e''))))) ,
                               step-⇓-trans (fst (snd (lower (h w'' e'')))) (snd (snd (snd (lower (h w'' e''))))))


equalTypes-#Σchoice-body : (i : ℕ) (w : 𝕎·) (c : Name) (k : ℕ)
                           → compatible· c w Resℕ
                           → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                           → equalInType i w' #NAT a₁ a₂
                                           → equalTypes i w' (#EQ (#APPLY (#CS c) a₁) (#NUM k) #QNAT)
                                                              (#EQ (#APPLY (#CS c) a₂) (#NUM k) #QNAT))
equalTypes-#Σchoice-body i w c k comp w' e' a₁ a₂ ea =
  eqTypesEQ← eqTypesQNAT aw1 aw2
  where
    j : inbar w' (λ w' _ → #strongMonEq w' a₁ a₂)
    j = equalInType-NAT→ i w' a₁ a₂ ea

    aw1 : equalInType i w' #QNAT (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
    aw1 = →equalInType-QNAT i w' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂) (Bar.inBar-idem barI (Bar.∀𝕎-inBarFunc barI aw11 j))
      where
        aw11 : ∀𝕎 w' (λ w'' e'' → #strongMonEq w'' a₁ a₂
                                 → inbar w'' (↑wPred' (λ w''' e → #weakMonEq w''' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)) e''))
        aw11 w'' e'' (m , c₁ , c₂) =
          inbar-wPred'-#weakMonEq w' w'' e'' (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
                                  (→inbar-#weakMonEq-APPLY-CS w'' a₁ a₂ m c c₁ c₂ (inbar-#weakMonEq-APPLY-CS w'' c m (⊑-compatible· (⊑-trans· e' e'') comp)))

    aw2 : equalInType i w' #QNAT (#NUM k) (#NUM k)
    aw2 = NUM-equalInType-QNAT i w' k



equalTypes-#Σchoice-body-sub0 : (i : ℕ) (w : 𝕎·) (c : Name) (k : ℕ)
                                → compatible· c w Resℕ
                                → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                                → equalInType i w' #NAT a₁ a₂
                                                → equalTypes i w' (sub0 a₁ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k) #[0]QNAT))
                                                                   (sub0 a₂ (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k) #[0]QNAT)))
equalTypes-#Σchoice-body-sub0 i w c k comp w' e' a₁ a₂ ea rewrite sub0-#Σchoice-body≡ a₁ c k | sub0-#Σchoice-body≡ a₂ c k =
  equalTypes-#Σchoice-body i w c k comp w' e' a₁ a₂ ea



equalInType-#Σchoice : {n i : ℕ} (p : i < n) (w : 𝕎·) (c : Name) (k : ℕ)
                       → compatible· c w Resℕ
                       → equalInType n w (#UNIV i) (#Σchoice c k) (#Σchoice c k)
equalInType-#Σchoice {n} {i} p w c k comp =
  equalTypes→equalInType-UNIV p (eqTypesSUM← {w} {i}
                                               {#NAT} {#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k) #[0]QNAT}
                                               {#NAT} {#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k) #[0]QNAT}
                                               (λ w' e' → eqTypesNAT) (equalTypes-#Σchoice-body-sub0 i w c k comp))


getChoice→equalInType-#Σchoice-aux2 : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℕ} (i : ℕ)
                                       → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getC n name w' ≡ just (NUM k)))
                                       → equalInType
                                           i w
                                           (#EQ (#APPLY (#CS name) (#NUM n)) (#NUM k) #QNAT)
                                           #AX #AX
getChoice→equalInType-#Σchoice-aux2 {n} {name} {w} {k} i g =
  equalInType-EQ eqTypesQNAT (Bar.∀𝕎-inBar barI aw)
  where
    aw : ∀𝕎 w (λ w' e → EQeq (#APPLY (#CS name) (#NUM n)) (#NUM k) (equalInType i w' #QNAT) w' #AX #AX)
    aw w' e = #compAllRefl #AX w' ,
              #compAllRefl #AX w' ,
              →equalInType-QNAT i w' (#APPLY (#CS name) (#NUM n)) (#NUM k) (Bar.∀𝕎-inBar barI aw')
      where
         aw' : ∀𝕎 w' (λ w'' _ → #weakMonEq w'' (#APPLY (#CS name) (#NUM n)) (#NUM k))
         aw' w2 e2 w3 e3 = lift (k , step-⇓-trans (lower (g w3 (⊑-trans· e (⊑-trans· e2 e3)))) (⇓-refl (NUM k) w3) , ⇓-refl (NUM k) w3)



getChoice→equalInType-#Σchoice-aux1 : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℕ} (i : ℕ)
                                       → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getC n name w' ≡ just (NUM k)))
                                       → equalInType
                                           i w
                                           (sub0 (#NUM n) (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (#[0]NUM k) #[0]QNAT))
                                           #AX #AX
getChoice→equalInType-#Σchoice-aux1 {n} {name} {w} {k} i g rewrite sub0-#Σchoice-body≡ (#NUM k) name k =
  getChoice→equalInType-#Σchoice-aux2 i g



getChoice→equalInType-#Σchoice-aux : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℕ} (i : ℕ)
                                      → compatible· name w Resℕ
                                      → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getC n name w' ≡ just (NUM k)))
                                      → equalInType
                                           i w
                                           (#SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (#[0]NUM k) #[0]QNAT))
                                           (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
getChoice→equalInType-#Σchoice-aux {n} {name} {w} {k} i comp g =
  equalInType-SUM
    {i} {w} {#NAT} {#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (#[0]NUM k) #[0]QNAT}
    (eqTypes-mon (uni i) eqTypesNAT)
    (equalTypes-#Σchoice-body-sub0 i w name k comp)
    j
  where
    j : inbar w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                 (λ a b ea → equalInType i w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) (#[0]NUM k) #[0]QNAT)))
                                 w'
                                 (#PAIR (#NUM n) #AX)
                                 (#PAIR (#NUM n) #AX))
    j = Bar.∀𝕎-inBar barI (λ w1 e1 → #NUM n , #NUM n , #AX , #AX ,
                                       NUM-equalInType-NAT i w1 n ,
                                       #compAllRefl (#PAIR (#NUM n) #AX) w1 ,
                                       #compAllRefl (#PAIR (#NUM n) #AX) w1 ,
                                       getChoice→equalInType-#Σchoice-aux1 i (∀𝕎-mon e1 g))
-- This last one is not true with references, but can be made true if we have a way to "freeze" a reference permanently,
-- and here 0 was "frozen"



getChoice→equalInType-#Σchoice : {n : ℕ} {name : Name} {w : 𝕎·} {k : ℕ} (i : ℕ)
                                  → compatible· name w Resℕ
                                  → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getC n name w' ≡ just (NUM k)))
                                  → equalInType i w (#Σchoice name k) (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
getChoice→equalInType-#Σchoice {n} {name} {w} {k} i comp g rewrite #Σchoice≡ name k = getChoice→equalInType-#Σchoice-aux i comp g


steps-APPLY-cs-forward : (w : 𝕎·) (n m : ℕ) (a b v : Term) (c : Name)
                         → isValue v
                         → steps n a w ≡ b
                         → steps m (APPLY (CS c) a) w ≡ v
                         → Σ ℕ (λ k → steps k (APPLY (CS c) b) w ≡ v)
steps-APPLY-cs-forward w 0 m a b v c isv c₁ c₂ rewrite c₁ = m , c₂
steps-APPLY-cs-forward w (suc n) 0 a b v c isv c₁ c₂ rewrite (sym c₂) = ⊥-elim isv
steps-APPLY-cs-forward w (suc n) (suc m) a b v c isv c₁ c₂ with step⊎ a w
... | inj₁ (u , p) rewrite p with is-NUM a
...                          | inj₁ (k , q) rewrite q | sym (just-inj p) | stepsVal (NUM k) w n tt | sym c₁ = suc m , c₂
...                          | inj₂ q rewrite step-APPLY-CS-¬NUM c a u w q p = steps-APPLY-cs-forward w n m u b v c isv c₁ c₂
steps-APPLY-cs-forward w (suc n) (suc m) a b v c isv c₁ c₂ | inj₂ p rewrite p | c₁ = suc m , c₂




-- TODO: generalize this so that (NUM i) is value
onlyℂ∈𝕎→≡-aux : {w : 𝕎·} {c : Name} {v : Term} {u : ℂ·} {k m : ℕ}
                  → onlyℂ∈𝕎 u c w
                  → steps k (APPLY (CS c) (NUM m)) w ≡ v
                  → isValue v
--                         → isValue u
                  → ℂ→T· u ⇓ v at w
onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {0} {m} oc c₁ isv {--isu--} rewrite sym c₁ = ⊥-elim isv
onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {suc k} {m} oc c₁ isv {--isu--}  with getChoice⊎ m c w
... | inj₁ (z , p) rewrite p | oc m z p {--| stepsVal u w k isu--} = k , c₁ -- sym c₁
... | inj₂ p rewrite p | sym c₁ = ⊥-elim isv



onlyℂ∈𝕎→≡ : {w : 𝕎·} {c : Name} {a v : Term} {u : ℂ·} {m : ℕ}
              → onlyℂ∈𝕎 u c w
              → a ⇓ NUM m at w
              → APPLY (CS c) a ⇓ v at w
              → isValue v
--                     → isValue u
--                     → v ≡ u
              → ℂ→T· u ⇓ v at w
onlyℂ∈𝕎→≡ {w} {c} {a} {v} {u} {m} oc c₁ c₂ isv {--isu--} =
  onlyℂ∈𝕎→≡-aux {w} {c} {v} {u} {k} {m} oc c₄ isv {--isu--}
  where
    c₃ : APPLY (CS c) (NUM m) ⇓ v at w
    c₃ = steps-APPLY-cs-forward w (fst c₁) (fst c₂) a (NUM m) v c isv (snd c₁) (snd c₂)

    k : ℕ
    k = fst c₃

    c₄ : steps k (APPLY (CS c) (NUM m)) w ≡ v
    c₄ = snd c₃


-- Without that it runs forever...
≡→⇓→⇓ : {w : 𝕎·} {a b c : Term}
         → b ≡ c
         → a ⇓ b at w
         → a ⇓ c at w
≡→⇓→⇓ {w} {a} {b} {c} h q rewrite h = q


≡NUM : {a b : ℕ} → a ≡ b → NUM a ≡ NUM b
≡NUM {a} {b} e rewrite e = refl



¬equalInType-#Σchoice : (i : ℕ) (w : 𝕎·) (r : Res) (c : Name) (x y : CTerm) {k1 : ℕ}
--                        → isValue (Res.def r)
                        → ∀𝕎 w (λ w' _ → Lift  (lsuc(L)) (¬ ℂ→T· (Res.def r) ⇓ NUM k1 at w'))
--                        → NUM k1 ≡ Res.def r
                        → onlyℂ∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → equalInType i w (#Σchoice c k1) x y
                        → ⊥
¬equalInType-#Σchoice i w r c x y {k1} {--isvd--} diff oc comp fb eqi = lower (diff w3 (⊑-trans· e1 (⊑-trans· e2 e3))) neq3
  where
    h0 : equalInType i w (#SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k1) #[0]QNAT)) x y
    h0 rewrite #Σchoice≡ c k1 = eqi

    h1 : inbar w (λ w' _ → SUMeq (equalInType i w' #NAT) (λ a b ea → equalInType i w' (#EQ (#APPLY (#CS c) a) (#NUM k1) #QNAT)) w' x y)
    h1 = Bar.∀𝕎-inBarFunc barI aw (equalInType-SUM→ {i} {w} {#NAT} {#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k1) #[0]QNAT} h0)
      where
        aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType i w' #NAT)
                                     (λ a b ea → equalInType i w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (#[0]NUM k1) #[0]QNAT)))
                                     w' x y
                           → SUMeq (equalInType i w' #NAT)
                                    (λ a b ea → equalInType i w' (#EQ (#APPLY (#CS c) a) (#NUM k1) #QNAT))
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

    h2 : SUMeq (equalInType i w1 #NAT) (λ a b ea → equalInType i w1 (#EQ (#APPLY (#CS c) a) (#NUM k1) #QNAT)) w1 x y
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

    eb1 : equalInType i w1 (#EQ (#APPLY (#CS c) a₁) (#NUM k1) #QNAT) b₁ b₂
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

    eb2 : equalInType i w2 (#EQ (#APPLY (#CS c) a₁) (#NUM k1) #QNAT) b₁ b₂
    eb2 = equalInType-mon eb1 w2 e2

    -- 3rd jump to bar
    eb3 : inbar w2 (λ w' _ → #weakMonEq w' (#APPLY (#CS c) a₁) (#NUM k1))
    eb3 = equalInType-EQ-QNAT→ {i} {w2} {#APPLY (#CS c) a₁} {#NUM k1} eb2

    w3 : 𝕎·
    w3 = fst (ChoiceBar.followChoice CB c eb3 oc2 comp2 fb2)

    e3 : w2 ⊑· w3
    e3 = fst (snd (ChoiceBar.followChoice CB c eb3 oc2 comp2 fb2))

    oc3 : onlyℂ∈𝕎 (Res.def r) c w3
    oc3 = fst (snd (snd (ChoiceBar.followChoice CB c eb3 oc2 comp2 fb2)))

    comp3 : compatible· c w3 r
    comp3 = fst (snd (snd (snd (ChoiceBar.followChoice CB c eb3 oc2 comp2 fb2))))

    fb3 : freezable· c w3
    fb3 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB c eb3 oc2 comp2 fb2)))))

    eb4 : #weakMonEq w3 (#APPLY (#CS c) a₁) (#NUM k1)
    eb4 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB c eb3 oc2 comp2 fb2)))))

    -- and now we conclude
    k : ℕ
    k = fst (#weakMonEq→ {w3} {#APPLY (#CS c) a₁} {#NUM k1} eb4)

    cn₁ : #APPLY (#CS c) a₁ #⇓ #NUM k at w3
    cn₁ = fst (snd (#weakMonEq→ {w3} {#APPLY (#CS c) a₁} {#NUM k1} eb4))

    cn₂ : #NUM k1 #⇓ #NUM k at w3
    cn₂ = snd (snd (#weakMonEq→ {w3} {#APPLY (#CS c) a₁} {#NUM k1} eb4))

    neq1 : ℂ→T· (Res.def r) ⇓ NUM k at w3
    neq1 = onlyℂ∈𝕎→≡ oc3 (lower (ca₁ w3 e3)) cn₁ tt {--isvd--}

    neq2 : k1 ≡ k
    neq2 = NUMinj (compVal (NUM k1) (NUM k) w3 cn₂ tt)

    neq3 : ℂ→T· (Res.def r) ⇓ NUM k1 at w3
    neq3 = ≡→⇓→⇓ (≡NUM (sym neq2)) neq1 -- rewrite sym neq2 = neq1



¬-ℕ→ℂ→T-⇓-NUM-1 : (w : 𝕎·) → ¬ ℂ→T· (ℕ→ℂ· 0) ⇓ NUM 1 at w
¬-ℕ→ℂ→T-⇓-NUM-1 w h rewrite ℕ→ℂ→T· 0 = ¬≡s 0 (NUMinj (compVal (NUM 0) (NUM 1) w h tt))



-- If we don't use this Agda gets stuck compiling...
∀𝕎-getChoice→getC : {w : 𝕎·} {n : ℕ} {name : Name} {k : ℕ}
                      → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getChoice· n name w' ≡ just (ℕ→ℂ· k)))
                      → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getC n name w' ≡ just (NUM k)))
∀𝕎-getChoice→getC {w} {n} {name} {k} aw w' e' rewrite lower (aw w' e') | ℕ→ℂ→T· k = lift refl



-- use equalInType-FUN instead
notClassical : (w : 𝕎·) {n i : ℕ} (p : i < n) → member w (#NEG (#LEM p)) #lamAX
notClassical w {n} {i} p =
  (n , equalInType-NEG (λ w1 e1 → eqTypesLem w1 p) aw1)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#LEM p) a₁ a₂)
    aw1 w1 e1 a₁ a₂ ea = concl h5
      where
        aw1' : equalInType n w1 (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))) a₁ a₂
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
        r = Resℕ

        w2 : 𝕎·
        w2 = startChoice· name r w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏· r w1

        k1 : ℕ
        k1 = 1 -- This has to be different from r's default value

        dks : ∀𝕎 w (λ w' _ → Lift  (lsuc(L)) (¬ ℂ→T· (Res.def r) ⇓ NUM k1 at w'))
        dks w' e = lift (λ x → ¬-ℕ→ℂ→T-⇓-NUM-1 w' x) --¬≡s 0 (sym (NUMinj e))

        -- instantiate aw5 with w2 (we also need a proof that (w1 ⊑ w2)) and (#Σchoice name k1)
        h1 : inbar w2 (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                               → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' (#Σchoice name k1) x y)
                                  ⊎
                                  (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w'
                                   × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂)))))))
        h1 = aw5 w2 e2 (#Σchoice name k1) (#Σchoice name k1) (equalInType-#Σchoice p w2 name k1 (startChoiceCompatible· r w1))

        oc1 : onlyℂ∈𝕎 (Res.def r) name w2
        oc1 n t e = getChoice-startNewChoice· n r w1 t e --rewrite getChoice-startNewChoice· n r w1 = ⊥-elim (¬just≡nothing (sym e))

        comp1 : compatible· name w2 r
        comp1 = startChoiceCompatible· r w1

        fb1 : freezable· name w2
        fb1 = freezableStart· r w1

        h2 : Σ 𝕎· (λ w3 → Σ (w2 ⊑· w3) (λ e3 → onlyℂ∈𝕎 (Res.def r) name w3 × compatible· name w3 Resℕ × freezable· name w3 ×
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

        -- 2nd injection:
        w5 : 𝕎·
        w5 = freeze· name w4 (ℕ→ℂ· k1)

        rNUM : (k : ℕ) → ·ᵣ r k (ℕ→ℂ· k1)
        rNUM k = k1 , refl

        e5 : w4 ⊑· w5
        e5 = freeze⊑· name w4 (ℕ→ℂ· k1) comp3 rNUM

        n1 : ℕ
        n1 = fst (getFreeze· name w4 (ℕ→ℂ· k1) comp3 fb3)

        g0 : ∀𝕎 w5 (λ w' _ → Lift (lsuc(L)) (getChoice· n1 name w' ≡ just (ℕ→ℂ· k1)))
        g0 = snd (getFreeze· name w4 (ℕ→ℂ· k1) comp3 fb3)

        g1 : ∀𝕎 w5 (λ w' _ → Lift (lsuc(L)) (getC n1 name w' ≡ just (NUM k1)))
        g1 = ∀𝕎-getChoice→getC g0

        h6 : equalInType i w5 (#Σchoice name k1) (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX)
        h6 = getChoice→equalInType-#Σchoice i (⊑-compatible· e5 comp3) g1

        e' : w ⊑· w4
        e' = ⊑-trans· (⊑-trans· (⊑-trans· e1 e2) e3) e4

        -- conclusion
        concl : ((t #⇛ (#INL x) at w4 × t #⇛ (#INL y) at w4 × equalInType i w4 (#Σchoice name k1) x y)
                 ⊎
                 (t #⇛ (#INR x) at w4 × t #⇛ (#INR y) at w4
                  × ∀𝕎 w4 (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂))) → ⊥
        concl (inj₁ (c₁ , c₂ , eqi)) = ¬equalInType-#Σchoice i w4 Resℕ name x y (∀𝕎-mon e' dks) oc3 comp3 fb3 eqi
        concl (inj₂ (c₁ , c₂ , aw)) = aw w5 e5 (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX) h6

\end{code}[hide]
