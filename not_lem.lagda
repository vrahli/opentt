\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module not_lem (bar : Bar) where

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
open import compatible
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar


module not_lem {L : Level} (W : PossibleWorlds {L})
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

open import choiceBarDef(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)

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
Σchoice : (n : Name) (k : ℂ·) → Term
Σchoice n k = SUM NAT (EQ (APPLY (CS n) (VAR 0)) (ℂ→T k) typeℂ₀₁)



#Σchoice : (n : Name) (k : ℂ·) → CTerm
#Σchoice n k = ct (Σchoice n k) c
  where
    c : # (Σchoice n k)
    c rewrite #-typeℂ₀₁ | #-ℂ→T k = refl


#Σchoice≡ : (n : Name) (k : ℂ·) → #Σchoice n k ≡ #SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS n) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)
#Σchoice≡ n k = CTerm≡ refl


sub0-#Σchoice-body≡ : (a : CTerm) (c : Name) (k : ℂ·)
                      → sub0 a (#[0]EQ (#[0]APPLY (#[0]CS c) #[0]VAR) (ℂ→C0 k) #[0]Typeℂ₀₁)
                         ≡ #EQ (#APPLY (#CS c) a) (ℂ→C· k) Typeℂ₀₁·
sub0-#Σchoice-body≡ a c k = CTerm≡ (→≡EQ (→≡APPLY refl (shiftDownUp ⌜ a ⌝ 0))
                                          (subNotIn ⌜ a ⌝ _ (CTerm.closed (ℂ→C· k)))
                                          (subNotIn ⌜ a ⌝ _ (CTerm.closed Typeℂ₀₁·)))



-- A short name
Resℂ : Res
Resℂ = Resℂ₀₁



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


∼ℂ≡-r : {c c1 c2 : ℂ·} → c1 ≡ c2 → ∼ℂ· c c1 → ∼ℂ· c c2
∼ℂ≡-r {c} {c1} {c2} e h rewrite e = h



¬equalInType-#Σchoice : (i : ℕ) (w : 𝕎·) (r : Res) (c : Name) (x y : CTerm) {k1 : ℂ·}
                        → isValue (ℂ→T (Res.def r))
                        → isValue (ℂ→T k1)
                        → ¬ ∼ℂ· (Res.def r) k1
                        → onlyℂ∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → equalInType i w (#Σchoice c k1) x y
                        → ⊥
¬equalInType-#Σchoice i w r c x y {k1} isv₁ isv₂ diff oc comp fb eqi = diff sim3
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

    k' : ℂ·
    k' = fst (snd (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7))

    cn₁ : #APPLY (#CS c) (#NUM m) #⇓ ℂ→C· k at w4
    cn₁ = fst (snd (snd (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7)))

    cn₂ : ℂ→C· k1 #⇓ ℂ→C· k' at w4
    cn₂ = fst (snd (snd (snd (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7))))

    sim1 : ∼ℂ· k k'
    sim1 = snd (snd (snd (snd (#weakℂEq→ {w4} {#APPLY (#CS c) (#NUM m)} {ℂ→C· k1} eb7))))

    gc2 : Σ ℂ· (λ t → getChoice· m c w4 ≡ just t)
    gc2 = lower (gc1 w4 (⊑-refl· _))

    cn₃ : ℂ→C· k #⇓ ℂ→C· (Res.def r) at w4
    cn₃ = onlyℂ∈𝕎→≡ oc4 cn₁ gc2 isv₁

    eq1 : ℂ→C· k1 ≡ ℂ→C· k'
    eq1 = CTerm≡ (compVal (ℂ→T k1) (ℂ→T k') w4 cn₂ isv₂)

    sim2 : ∼ℂ· k k1
    sim2 = ∼ℂ≡-r (sym (ℂ→C-inj· eq1)) sim1

    sim3 : ∼ℂ· (Res.def r) k1
    sim3 = ℂ→C→∼ℂ· cn₃ sim2

{--
-------
    cn₄ : ℂ→C· k1 #⇓ ℂ→C· (Res.def r) at w4
    cn₄ = ⇓-trans cn₂ cn₃

    cn₅ : ℂ→C· k1 ≡ ℂ→C· (Res.def r)
    cn₅ = CTerm≡ (compVal (ℂ→T k1) (ℂ→T (Res.def r)) w4 cn₄ isv₂)
--}



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


equalInType-SQUASH-UNION-LIFT→ :  {n i : ℕ} (p : i < n) {w : 𝕎·} {a b u v : CTerm}
                                  → equalInType n w (#SQUASH (#UNION (#↑T p a) (#NEG (#↑T p b)))) u v
                                  → equalInType i w (#SQUASH (#UNION a (#NEG b))) #AX #AX
equalInType-SQUASH-UNION-LIFT→ {n} {i} p {w} {a} {b} {u} {v} eqi =
  →equalInType-SQUASH
    (Bar.∀𝕎-inBar barI (λ w' _ → #⇛-refl w' #AX))
    (Bar.∀𝕎-inBar barI (λ w' _ → #⇛-refl w' #AX))
    j1
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → equalInType n w' (#UNION (#↑T p a) (#NEG (#↑T p b))) t t)
                        → Σ CTerm (λ t → equalInType i w' (#UNION a (#NEG b)) t t))
    aw w' e (t , eqj) = t , →equalInType-UNION (equalTypes-#↑T→ p w' a a (equalInType-UNION→₁ eqj))
                                               (eqTypesNEG← (equalTypes-#↑T→ p w' b b (eqTypesNEG→ (equalInType-UNION→₂ {n} {w'} {#↑T p a} {#NEG (#↑T p b)} {t} {t} eqj))))
                                               (Bar.∀𝕎-inBarFunc barI aw1 equ)
      where
        equ : inbar w' (λ w'' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (t #⇛ (#INL x) at w'' × t #⇛ (#INL y) at w'' × equalInType n w'' (#↑T p a) x y)
                                             ⊎
                                             (t #⇛ (#INR x) at w'' × t #⇛ (#INR y) at w'' × equalInType n w'' (#NEG (#↑T p b)) x y))))
        equ = equalInType-UNION→ eqj

        aw1 : ∀𝕎 w' (λ w'' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                                   (t #⇛ #INL x at w'' × t #⇛ #INL y at w'' × equalInType n w'' (#↑T p a) x y)
                                   ⊎ (t #⇛ #INR x at w'' × t #⇛ #INR y at w'' × equalInType n w'' (#NEG (#↑T p b)) x y)))
                              → Σ CTerm (λ x → Σ CTerm (λ y →
                                  (t #⇛ #INL x at w'' × t #⇛ #INL y at w'' × equalInType i w'' a x y)
                                  ⊎ (t #⇛ #INR x at w'' × t #⇛ #INR y at w'' × equalInType i w'' (#NEG b) x y))))
        aw1 w'' e' (x , y , inj₁ (c₁ , c₂ , eqk)) = x , y , inj₁ (c₁ , c₂ , equalInType-#↑T→ p w'' a x y eqk)
        aw1 w'' e' (x , y , inj₂ (c₁ , c₂ , eqk)) = x , y , inj₂ (c₁ , c₂ , equalInType-NEG (λ w0 e0 → equalTypes-#↑T→ p w0 b b (eqTypes-mon (uni n) (eqTypesNEG→ (fst eqk)) w0 e0)) (equalInType-NEG-↑T→ p eqk))

    j0 : inbar w (λ w' _ → Σ CTerm (λ t → equalInType n w' (#UNION (#↑T p a) (#NEG (#↑T p b))) t t))
    j0 = equalInType-SQUASH→ eqi

    j1 : inbar w (λ w' _ → Σ CTerm (λ t → equalInType i w' (#UNION a (#NEG b)) t t))
    j1 = Bar.∀𝕎-inBarFunc barI aw j0



equalInType-SQUASH-UNION→ : {i : ℕ} {w : 𝕎·} {a b u v : CTerm}
                             → equalInType i w (#SQUASH (#UNION a (#NEG b))) u v
                             → inbar w (λ w' _ → inhType i w' a ⊎ ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' b a₁ a₂))
equalInType-SQUASH-UNION→ {i} {w} {a} {b} {u} {v} eqi =
  Bar.inBar-idem barI (Bar.∀𝕎-inBarFunc barI aw1 h3)
  where
    h1 : inbar w (λ w' _ → Σ CTerm (λ t → equalInType i w' (#UNION a (#NEG b)) t t))
    h1 = equalInType-SQUASH→ eqi

    h2 : inbar w (λ w' _ → Σ CTerm (λ t → inbar w' (λ w'' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                         → (t #⇛ (#INL x) at w'' × t #⇛ (#INL y) at w'' × equalInType i w'' a x y)
                                            ⊎
                                            (t #⇛ (#INR x) at w'' × t #⇛ (#INR y) at w'' × equalInType i w'' (#NEG b) x y))))))
    h2 = Bar.∀𝕎-inBarFunc barI (λ w' e (t , eqj) → t , equalInType-UNION→ eqj) h1

    h3 : inbar w (λ w' _ → Σ CTerm (λ t → inbar w' (λ w'' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                         → (t #⇛ (#INL x) at w'' × t #⇛ (#INL y) at w'' × equalInType i w'' a x y)
                                            ⊎
                                            (t #⇛ (#INR x) at w'' × t #⇛ (#INR y) at w''
                                              × ∀𝕎 w'' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂)))))))
    h3 = Bar.∀𝕎-inBarFunc barI (λ w1 e1 (t , eqt) → t , Bar.∀𝕎-inBarFunc barI (λ { w3 e3 (x , y , inj₁ (c₁ , c₂ , z)) → x , y , inj₁ (c₁ , c₂ , z) ;
                                                                                     w3 e3 (x , y , inj₂ (c₁ , c₂ , z)) → x , y , inj₂ (c₁ , c₂ , equalInType-NEG→ z) }) eqt) h2

    aw1 : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → inbar w' (λ w'' _ → Σ CTerm (λ x →  Σ CTerm (λ y →
                            (t #⇛ #INL x at w'' × t #⇛ #INL y at w'' × equalInType i w'' a x y)
                            ⊎ (t #⇛ #INR x at w'' × t #⇛ #INR y at w'' × ∀𝕎 w'' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂))))))
                        → inbar w' (↑wPred' (λ w'' e →  inhType i w'' a ⊎ ∀𝕎 w'' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂)) e'))
    aw1 w1 e1 (t , j) = Bar.inBar-idem barI (Bar.∀𝕎-inBarFunc barI aw2 j)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                                 (t #⇛ #INL x at w' × t #⇛ #INL y at w' × equalInType i w' a x y)
                                 ⊎ (t #⇛ #INR x at w' × t #⇛ #INR y at w' × ∀𝕎 w' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂))))
                             → inbar w' (↑wPred' (λ w'' e → ↑wPred' (λ w''' e₁ → inhType i w''' a ⊎ ∀𝕎 w''' (λ w'''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'''' b a₁ a₂)) e1 w'' e) e'))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , z)) = Bar.∀𝕎-inBar barI (λ w3 e3 x₁ x₂ → inj₁ (x , equalInType-mon (equalInType-refl z) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , z)) = Bar.∀𝕎-inBar barI (λ w3 e3 x₁ x₂ → inj₂ (∀𝕎-mon e3 z))



¬LEM : (w : 𝕎·) {n i : ℕ} (p : i < n) → member w (#NEG (#LEM p)) #lamAX
¬LEM w {n} {i} p =
  (n , equalInType-NEG (λ w1 e1 → eqTypesLem w1 p) aw1)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#LEM p) a₁ a₂)
    aw1 w1 e1 a₁ a₂ ea = concl h3
      where
        aw1' : equalInType n w1 (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))) a₁ a₂
        aw1' rewrite #LEM≡#PI p = ea

        aw2 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → equalInType n w' (#SQUASH (#UNION (#↑T p u₁) (#NEG (#↑T p u₁)))) (#APPLY a₁ u₁) (#APPLY a₂ u₂))
        aw2 w' e' u₁ u₂ j = ≡CTerm→equalInType (sub0-#[0]SQUASH-LEM p u₁) (snd (snd (equalInType-PI→ aw1')) w' e' u₁ u₂ j)

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

        dks : ¬ ∼ℂ· (Res.def r) k1
        dks = ¬∼ℂ₀₁·

        h1 : equalInType i w2 (#SQUASH (#UNION (#Σchoice name k1) (#NEG (#Σchoice name k1)))) #AX #AX
        h1 = equalInType-SQUASH-UNION-LIFT→ p (aw2 w2 e2 (#Σchoice name k1) (#Σchoice name k1) (equalInType-#Σchoice p w2 name k1 (startChoiceCompatible· r w1) Σsat-ℂ₁))

        h2 : inbar w2 (λ w' _ → inhType i w' (#Σchoice name k1) ⊎ ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂))
        h2 = equalInType-SQUASH-UNION→ h1

        oc1 : onlyℂ∈𝕎 (Res.def r) name w2
        oc1 n = getChoice-startNewChoice· n r w1 --rewrite getChoice-startNewChoice· n r w1 = ⊥-elim (¬just≡nothing (sym e))

        comp1 : compatible· name w2 r
        comp1 = startChoiceCompatible· r w1

        fb1 : freezable· name w2
        fb1 = freezableStart· r w1

        -- We follow the choice
        w3 : 𝕎·
        w3 = fst (ChoiceBar.followChoice CB name h2 oc1 comp1 fb1)

        e3 : w2 ⊑· w3
        e3 = fst (snd (ChoiceBar.followChoice CB name h2 oc1 comp1 fb1))

        oc2 : onlyℂ∈𝕎 (Res.def r) name w3
        oc2 = fst (snd (snd (ChoiceBar.followChoice CB name h2 oc1 comp1 fb1)))

        comp2 : compatible· name w3 r
        comp2 = fst (snd (snd (snd (ChoiceBar.followChoice CB name h2 oc1 comp1 fb1))))

        fb2 : freezable· name w3
        fb2 = fst (snd (snd (snd (snd (ChoiceBar.followChoice CB name h2 oc1 comp1 fb1)))))

        h3 : inhType i w3 (#Σchoice name k1) ⊎ ∀𝕎 w3 (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂)
        h3 = snd (snd (snd (snd (snd (ChoiceBar.followChoice CB name h2 oc1 comp1 fb1)))))

        -- 1st injection: proved by ¬equalInType-#Σchoice
        -- For this it is enough to be able to make a choice different from k1 forever, for example choosing 0 forever

        -- 2nd injection:
        -- This is where we should be able to make another choice than the default choice
        w4 : 𝕎·
        w4 = freeze· name w3 k1

        rNUM : ⋆ᵣ r k1
        rNUM = sat-ℂ₁

        e4 : w3 ⊑· w4
        e4 = freeze⊑· name w3 k1 comp2 rNUM

        n1 : ℕ
        n1 = fst (getFreeze· name w3 k1 comp2 fb2)

        g0 : ∀𝕎 w4 (λ w' _ → Lift (lsuc(L)) (getChoice· n1 name w' ≡ just k1))
        g0 = snd (getFreeze· name w3 k1 comp2 fb2)

        g1 : #APPLY (#CS name) (#NUM n1) #⇛ ℂ→C· k1 at w4
        g1 = →#APPLY-#CS#⇛ℂ→C· g0

        h4 : equalInType i w4 (#Σchoice name k1) (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX)
        h4 = getChoice→equalInType-#Σchoice i (⊑-compatible· e4 comp2) (sat-ℂ₁ 0) g1

        e' : w ⊑· w3
        e' = ⊑-trans· (⊑-trans· e1 e2) e3

        -- conclusion
        concl : (inhType i w3 (#Σchoice name k1) ⊎ ∀𝕎 w3 (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' (#Σchoice name k1) a₁ a₂))
                → ⊥
        concl (inj₁ (t , eqi)) = ¬equalInType-#Σchoice i w3 Resℂ name t t isValueℂ₀· isValueℂ₁· dks oc2 comp2 fb2 eqi
        concl (inj₂ aw) = aw w4 e4 (#PAIR (#NUM n1) #AX) (#PAIR (#NUM n1) #AX) h4

\end{code}[hide]
