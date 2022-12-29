\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
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
open import progress
open import freeze
open import newChoice
open import mod
open import choiceBar


module continuity1 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G)
                   (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import terms7(W)(C)(K)(G)(X)(N)

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

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)



-------------------------
-- SOME ASSUMPTIONS
-- The modality is Kripke-like
K□ : Set(lsuc(lsuc(L)))
K□ = {w : 𝕎·} {f : wPred w} → □· w f → ∀𝕎 w f


-- the modality is non-empty
∃□ : Set(lsuc(lsuc(L)))
∃□ = {w : 𝕎·} {f : wPred w} → □· w f → ∃𝕎 w f
-------------------------




-- turns 'f' into λy.(if n ≤ y then name:=ℂ₁);f(y)
-- ℂ₀ is treated as true here (i.e., "didn't reach n"), and ℂ₁ as false (i.e., "reached at least n")
bound : (name : Name) (n : Term) (f : Term) → Term
bound name n f = LAMBDA (SEQ (IFLE n (VAR 0) (CHOOSE (NAME name) (ℂ→T ℂ₁·)) AX) (APPLY f (VAR 0)))


-- TODO: the name should be a fresh name, that does not occur in F
-- TODO: need union types?


set : (name : Name) → Term
set name = CHOOSE (NAME name) (ℂ→T ℂ₀·)


-- Assuming that choices are numbers
--IFC0 : Term → Term → Term → Term
--IFC0 a b c = IFLT (get0 name) (NUM 1)



probe : (name : Name) (F : Term) (n : Term) (f : Term) → Term
probe name F n f = LET (APPLY F (bound name n f))
                       (IFLT (get0 name) (NUM 1) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains 0 (i.e., < 1 -- we assume here that choices are numbers)


oldtest : (name : Name) (F : Term) (n : Term) (f : Term) → Term
oldtest name F n f = LET (APPLY F (bound name n f))
                         (LET (IFLT (get0 name) (NUM 1) (INL (VAR 0)) (INR AX)) -- We check whether 'name' contains ℂ₀
                              (SEQ (set name) -- resets the reference to ℂ₀
                                   (VAR 0)))


test : (name : Name) (F : Term) (n : Term) (f : Term) → Term
test name F n f = SEQ (set name) (probe name F n f)


set0 : (name : Name) → Term
set0 name = setT name (NUM 0)


appUpd : (name : Name) (F f : Term) → Term
appUpd name F f = APPLY F (upd name f)


probeM : (name : Name) (F f : Term) → Term
probeM name F f = SEQ (appUpd name F f) (SUC (get0 name))


testM : (name : Name) (F f : Term) → Term
testM name F f = SEQ (set0 name) (probeM name F f)


νtestM : (F f : Term) → Term
νtestM F f = FRESH (testM 0 F f)


-- TODO:
-- We need to truncate this type using SUBSING
-- Then, prove that testM is a NAT
-- We will need:
--  + to assume that the choice is over nats
--  + that it's actually a time invariant nat, which requires
--    * F and f to not read choices, but they can write
contBody : (F f : Term) → Term
contBody F f =
  SUM NAT
      (PI BAIRE
          (FUN (FFDEFS BAIRE (VAR 0))
               (FUN (EQ f (VAR 0) (BAIREn (VAR 1)))
                    (EQ (APPLY F f) (APPLY F (VAR 0)) NAT))))



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



#νtestM : (F f : CTerm) → CTerm
#νtestM F f = ct (νtestM ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # νtestM ⌜ F ⌝ ⌜ f ⌝
    c = CTerm.closed (#testM 0 F f)



#[0]AX : CTerm0
#[0]AX = ct0 AX refl


#BOUND : (name : Name) (n : CTerm) (f : CTerm) → CTerm
#BOUND name n f =
  #LAMBDA (#[0]SEQ (#[0]IFLE ⌞ n ⌟ #[0]VAR (#[0]CHOOSE (#[0]NAME name) ⌞ ℂ→C· ℂ₁· ⌟) #[0]AX)
                   (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#bound≡ : (name : Name) (n : CTerm) (f : CTerm) → #bound name n f ≡ #BOUND name n f
#bound≡ name n f = CTerm≡ refl



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


#probeM≡ : (name : Name) (F f : CTerm) → #probeM name F f ≡ #SEQ (#APPLY F (#upd name f)) (#SUC (#get0 name))
#probeM≡ name F f = CTerm≡ refl


#testM≡ : (name : Name) (F f : CTerm) → #testM name F f ≡ #SEQ (#set0 name) (#probeM name F f)
#testM≡ name F f = CTerm≡ refl


--→≡APPLY : {a₁ a₂ b₁ b₂ : Term} → a₁ ≡ a₂ → b₁ ≡ b₂ → APPLY a₁ b₁ ≡ APPLY a₂ b₂
--→≡APPLY e f rewrite e | f = refl



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


eqTypesBAIRE : {w : 𝕎·} {i : ℕ} → isType i w #BAIRE
eqTypesBAIRE {w} {i} = ≡CTerm→eqTypes (sym #BAIRE≡) (sym #BAIRE≡) (eqTypesFUN← eqTypesNAT eqTypesNAT)




bound∈ : (i : ℕ) (w : 𝕎·) (name : Name) (n : CTerm) (f : CTerm)
         → ∈Type i w #NAT n
         → ∈Type i w #BAIRE f
         → ∈Type i w #BAIRE (#bound name n f)
bound∈ i w name n f ∈n ∈f =
  ≡CTerm→equalInTypeₗ (sym (#bound≡ name n f)) (≡CTerm→equalInTypeᵣ (sym (#bound≡ name n f)) (≡CTerm→equalInType (sym #BAIRE≡) eqi))
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY (#BOUND name n f) a₁) (#APPLY (#BOUND name n f) a₂))
    aw w1 e1 a₁ a₂ ea =
      equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev
        _ equalTerms-pres-#⇛-left-rev-NAT
        (#⇛!-#APPLY-#BOUND w1 name n f a₁) (#⇛!-#APPLY-#BOUND w1 name n f a₂) eqi1
--equalInType-#⇛-LR-rev (#⇛!-#APPLY-#BOUND w1 name n f a₁) (#⇛!-#APPLY-#BOUND w1 name n f a₂) eqi1
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
    eqi = equalInType-FUN eqTypesNAT eqTypesNAT aw



APPLY-bound∈ : (i : ℕ) (w : 𝕎·) (F : CTerm) (name : Name) (n : CTerm) (f : CTerm)
               → ∈Type i w #BAIRE→NAT F
               → ∈Type i w #NAT n
               → ∈Type i w #BAIRE f
               → ∈Type i w #NAT (#APPLY F (#bound name n f))
APPLY-bound∈ i w F name n f ∈F ∈n ∈f =
  equalInType-FUN→
    {i} {w} {#BAIRE} {#NAT} {F} {F} ∈F w (⊑-refl· _) (#bound name n f) (#bound name n f)
    (bound∈ i w name n f ∈n ∈f)






sub-num-probe-body : {m : ℕ} {name : Name}
                     → sub (NUM m) (IFLT (get0 name) (NUM 1) (INL (VAR 0)) (INR AX))
                        ≡ IFLT (get0 name) (NUM 1) (INL (NUM m)) (INR AX)
sub-num-probe-body {m} {name} = refl




{--
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
--}


getChoice→getT : {n : ℕ} {name : Name} {w : 𝕎·} {c : ℂ·}
                  → getChoice· n name w ≡ just c
                  → getT n name w ≡ just ⌜ ℂ→C· c ⌝
getChoice→getT {n} {name} {w} {c} getc rewrite getc = refl



≡ℂ→≡ℂ→C : {a b : ℂ·}
             → a ≡ b
             → ℂ→C· a ≡ ℂ→C· b
≡ℂ→≡ℂ→C {a} {b} e rewrite e = refl



{--
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
--}



{--
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
--}


{--
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
--}


{--
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
--}



{--
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
--}


-- Prove this for the current world, and show that if F and f cannot read then this is true for all extensions too

-- Do we need to constrain F's type to be in (BAIRE→NAT!)? -- No, doesn't make sense: what function is going to inhabit that type?

-- Check what world (#APPLY F (#bound name n f)) ends up in and name's value in that world
-- and compare it with with ℂ₀ before instantiating the conclusion
-- Because we used NAT, this requires choices to be numbers (should be QTNAT in the union)




#⇛!-#APPLY-#UPD : (w : 𝕎·) (name : Name) (f : CTerm) (a : CTerm)
                   → #APPLY (#UPD name f) a #⇛! #LET a (#[0]SEQ (#[0]updGt name #[0]VAR) (#[0]APPLY ⌞ f ⌟ #[0]VAR)) at w
#⇛!-#APPLY-#UPD w name f a w1 e1
  = lift (1 , →≡pair (→sub-LET {⌜ a ⌝} {⌜ #[0]VAR ⌝} {⌜ #[1]SEQ (#[1]updGt name #[1]VAR0) (#[1]APPLY ⌞ f ⌟ #[1]VAR0) ⌝}
                                 (CTerm.closed a)
                                 (sub-VAR0 ⌜ a ⌝)
                                 (→≡LET refl (→≡APPLY e refl)))
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




updGt⇛AX : {w : 𝕎·} {name : Name} {m : ℕ}
            → ∀𝕎-get0-NUM w name
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
              → ∀𝕎-get0-NUM w name
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
       → ∀𝕎-get0-NUM w name
       → ∈Type i w #BAIRE f
       → ∈Type i w #BAIRE (#upd name f)
upd∈ i w name f g0 ∈f = ≡CTerm→∈Type (sym (#upd≡ name f)) (≡CTerm→equalInType (sym #BAIRE≡) eqi)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY (#UPD name f) a₁) (#APPLY (#UPD name f) a₂))
    aw w1 e1 a₁ a₂ ea =
      equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev
        _ equalTerms-pres-#⇛-left-rev-NAT
        (#⇛!-#APPLY-#UPD w1 name f a₁) (#⇛!-#APPLY-#UPD w1 name f a₂) eqi1
--equalInType-#⇛-LR-rev (#⇛!-#APPLY-#UPD w1 name f a₁) (#⇛!-#APPLY-#UPD w1 name f a₂) eqi1
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
    eqi = equalInType-FUN eqTypesNAT eqTypesNAT aw


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


{--
¬read-upd≡ : (name : Name) (f : Term) → ¬read (upd name f) ≡ ¬read f
¬read-upd≡ name f = {!refl!}
--}



∀𝕎-getT0-NUM→∀𝕎get0-NUM : (w : 𝕎·) (name : Name)
                            → ∀𝕎-get0-NUM w name
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



⇓NUM→SUC⇓NUM : {a : Term} {n : ℕ} {w1 w2 : 𝕎·}
                → a ⇓ NUM n from w1 to w2
                → SUC a ⇓ NUM (suc n) from w1 to w2
⇓NUM→SUC⇓NUM {a} {n} {w1} {w2} comp =
  ⇓-trans₂ {w1} {w2} {w2} {SUC a} {SUC (NUM n)} {NUM (suc n)} (SUC⇓ comp) (SUC-NUM⇓ w2 n)




-- TODO: now we ned to prove that testM computes to the same number in all extensions of w
-- (as long as name does not occur in F or f)
⇓APPLY-upd→⇓testM : (cn : comp→∀ℕ) (kb : K□) (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
                     → ∈Type i w #BAIRE→NAT F
                     → ∈Type i w #BAIRE f
                     → compatible· name w Res⊤
                     → Σ ℕ (λ k → testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) at w)
⇓APPLY-upd→⇓testM cn kb i w name F f ∈F ∈f {--nrF nrf gcn--} comp =
  fst cg , ⇓-from-to→⇓ {w} {fst ca} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (suc (fst cg))}
                       (⇓-trans₂ {w} {chooseT name w (NUM 0)} {fst ca} {testM name ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {NUM (suc (fst cg))}
                                 (SEQ⇓₁ {w} {chooseT name w (NUM 0)} {set0 name} {AX} {probeM name ⌜ F ⌝ ⌜ f ⌝} cs)
                                 (⇓-trans₂ {chooseT name w (NUM 0)} {chooseT name w (NUM 0)} {fst ca} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {probeM name ⌜ F ⌝ ⌜ f ⌝} {NUM (suc (fst cg))}
                                           (SEQ-AX⇓₁from-to (CTerm.closed (#probeM name F f)))
                                           (⇓-trans₂ {chooseT name w (NUM 0)} {fst ca} {fst ca} {probeM name ⌜ F ⌝ ⌜ f ⌝} {SEQ (NUM m) (SUC (get0 name))} {NUM (suc (fst cg))}
                                                     (SEQ⇓₁ (snd ca))
                                                     (⇓-trans₂ {proj₁ ca} {proj₁ ca} {proj₁ ca} {SEQ (NUM m) (SUC (get0 name))} {SUC (get0 name)} {NUM (suc (fst cg))}
                                                               (SEQ-val⇓₁from-to refl tt)
                                                               (⇓NUM→SUC⇓NUM (snd cg))))))
  where
    w1 : 𝕎·
    w1 = chooseT name w (NUM 0)

    cs : set0 name ⇓ AX from w to w1
    cs = 1 , refl

    e1 : w ⊑· w1
    e1 = ⇓from-to→⊑ {w} {w1} cs

    g0 : ∀𝕎-get0-NUM w1 name
    g0 = cn name w 0 comp

    eqa : ∈Type i w1 #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→
            (equalInType-mon ∈F w1 e1) w1 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w1 name f (cn name w 0 comp) (equalInType-mon ∈f w1 e1))

    eqn : NATeq w1 (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
    eqn = kb (equalInType-NAT→ i w1 (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa) w1 (⊑-refl· _)

    cak : Σ ℕ (λ k → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇛ NUM k at w1)
    cak = fst eqn , fst (snd eqn)

    m : ℕ
    m = fst cak

    ca : Σ 𝕎· (λ w' → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from w1 to w')
    ca = ⇛→⇓from-to (snd cak)

    e2 : w1 ⊑· fst ca
    e2 = ⇓from-to→⊑ {w1} {fst ca} (snd ca)

    cg : Σ ℕ (λ k → get0 name ⇓ NUM k from (fst ca) to (fst ca))
    cg = lower (∀𝕎-getT0-NUM→∀𝕎get0-NUM w1 name g0 (fst ca) e2)
-- TODO: add a 'fresh' to testM, and make it so that it adds an "entry" in the world
-- change choose so that the name is directly a parameter?


¬Names→⇓ : (w1 w2 w3 : 𝕎·) (t u : Term)
            → ¬Names t
            → t ⇓ u from w1 to w2
            → t ⇓ u from w3 to w3
¬Names→⇓ w1 w2 w3 t u nnt (k , c) = k , fst (¬Names→steps k w1 w2 w3 t u nnt c)



differ⇓from-to : (gc0 : get-choose-ℕ) (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name)
                 (w1 w2 w1' : 𝕎·) (a b v : Term)
                 → isValue v
                 → compatible· name1 w1 Res⊤
                 → compatible· name2 w1' Res⊤
                 → ∀𝕎-get0-NUM w1 name1
                 → differ name1 name2 f a b
                 → getT 0 name1 w1 ≡ getT 0 name2 w1'
                 → a ⇓ v from w1 to w2
                 → Σ 𝕎· (λ w2' → Σ Term (λ v' →
                     b ⇓ v' from w1' to w2' × differ name1 name2 f v v' × getT 0 name1 w2 ≡ getT 0 name2 w2'))
differ⇓from-to gc0 f cf nnf name1 name2 w1 w2 w1' a b v isv compat1 compat2 gt0n diff eqget comp =
  differ⇓ gc0 f cf nnf name1 name2 (fst comp) w1 w2 w1' a b v isv compat1 compat2 gt0n diff eqget (snd comp)



⇓APPLY-upd→⇓testM-name-free : (gc : get-choose-ℕ) (cn : comp→∀ℕ) (exb : ∃□)
                              (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
                              → #¬Names F
                              → #¬Names f
                              → ∈Type i w #BAIRE→NAT F
                              → ∈Type i w #BAIRE f
                              → compatible· name w Res⊤
                              → Σ ℕ (λ k → testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) at w)
⇓APPLY-upd→⇓testM-name-free gc cn exb i w name F f nnF nnf ∈F ∈f {--nrF nrf gcn--} comp =
  fst cg , ⇓-from-to→⇓ {w} {w1'} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (suc (fst cg))}
                       (⇓-trans₂ {w} {chooseT name w (NUM 0)} {w1'} {testM name ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {NUM (suc (fst cg))}
                                 (SEQ⇓₁ {w} {chooseT name w (NUM 0)} {set0 name} {AX} {probeM name ⌜ F ⌝ ⌜ f ⌝} cs)
                                 (⇓-trans₂ {chooseT name w (NUM 0)} {chooseT name w (NUM 0)} {w1'} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {probeM name ⌜ F ⌝ ⌜ f ⌝} {NUM (suc (fst cg))}
                                           (SEQ-AX⇓₁from-to (CTerm.closed (#probeM name F f)))
                                           (⇓-trans₂ {chooseT name w (NUM 0)} {w1'} {w1'} {probeM name ⌜ F ⌝ ⌜ f ⌝} {SEQ (NUM m) (SUC (get0 name))} {NUM (suc (fst cg))}
                                                     (SEQ⇓₁ ca4)
                                                     (⇓-trans₂ {w1'} {w1'} {w1'} {SEQ (NUM m) (SUC (get0 name))} {SUC (get0 name)} {NUM (suc (fst cg))}
                                                               (SEQ-val⇓₁from-to refl tt)
                                                               (⇓NUM→SUC⇓NUM (snd cg))))))
  where
    w1 : 𝕎·
    w1 = chooseT name w (NUM 0)

    cs : set0 name ⇓ AX from w to w1
    cs = 1 , refl

    e1 : w ⊑· w1
    e1 = ⇓from-to→⊑ {w} {w1} cs

    g0 : ∀𝕎-get0-NUM w1 name
    g0 = cn name w 0 comp

    eqa : ∈Type i w1 #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→
            (equalInType-mon ∈F w1 e1) w1 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w1 name f (cn name w 0 comp) (equalInType-mon ∈f w1 e1))

    eqn1 : □· w1 (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#upd name f)))
    eqn1 = equalInType-NAT→ i w1 (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa

    eqn2 : ∃𝕎 w1 (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#upd name f)))
    eqn2 = exb eqn1

    wx1 : 𝕎·
    wx1 = fst eqn2

    ex1 : w1 ⊑· wx1
    ex1 = fst (snd eqn2)

    eqn3 : NATeq wx1 (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
    eqn3 = snd (snd eqn2)

    cak : Σ ℕ (λ k → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇛ NUM k at wx1)
    cak = fst eqn3 , fst (snd eqn3)

    m : ℕ
    m = fst cak

    ca : Σ 𝕎· (λ w' → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from wx1 to w')
    ca = ⇛→⇓from-to (snd cak)

    w2 : 𝕎·
    w2 = fst ca

    ca2 : APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from wx1 to w2
    ca2 = snd ca

    ca3 : Σ 𝕎· (λ w1' → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from w1 to w1')
    ca3 = differNF⇓APPLY-upd gc ⌜ F ⌝  ⌜ f ⌝ (CTerm.closed f) name m wx1 w2 w1 nnF nnf
                             (⊑-compatible· (⊑-trans· e1 ex1) comp) (⊑-compatible· e1 comp)
                             (∀𝕎-mon ex1 g0) g0 ca2

    w1' : 𝕎·
    w1' = fst ca3

    ca4 : APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from w1 to w1'
    ca4 = snd ca3

    e2 : w1 ⊑· w1'
    e2 = ⇓from-to→⊑ {w1} {w1'} ca4

    cg : Σ ℕ (λ k → get0 name ⇓ NUM k from w1' to w1')
    cg = lower (∀𝕎-getT0-NUM→∀𝕎get0-NUM w1 name g0 w1' e2)



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


⇓APPLY-upd→⇓νtestM : (cn : comp→∀ℕ) (kb : K□) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                      → ∈Type i w #BAIRE→NAT F
                      → ∈Type i w #BAIRE f
                      → Σ ℕ (λ k → νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ NUM (suc k) at w)
⇓APPLY-upd→⇓νtestM cn kb i w F f ∈F ∈f =
  fst z , step-⇓-trans s1 (snd z)
  where
    tM : Term
    tM = testM 0 (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : step (νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)) w ≡ just (testM name ⌜ F ⌝ ⌜ f ⌝ , w1)
    s1 = ≡just (≡pair (shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl)

    z : Σ ℕ (λ k → testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) at w1)
    z = ⇓APPLY-upd→⇓testM cn kb i w1 name F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) comp1



⇓APPLY-upd→⇓νtestM-name-free : (gc : get-choose-ℕ) (cn : comp→∀ℕ) (exb : ∃□) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                               → #¬Names F
                               → #¬Names f
                               → ∈Type i w #BAIRE→NAT F
                               → ∈Type i w #BAIRE f
                               → Σ ℕ (λ k → νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ NUM (suc k) at w)
⇓APPLY-upd→⇓νtestM-name-free gc cn exb i w F f nnF nnf ∈F ∈f =
  fst z , step-⇓-trans s1 (snd z)
  where
    tM : Term
    tM = testM 0 (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : step (νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)) w ≡ just (testM name ⌜ F ⌝ ⌜ f ⌝ , w1)
    s1 = ≡just (≡pair (shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl)

    z : Σ ℕ (λ k → testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) at w1)
    z = ⇓APPLY-upd→⇓testM-name-free gc cn exb i w1 name F f nnF nnf (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) comp1



#shiftNameUp : ℕ → CTerm → CTerm
#shiftNameUp n t = ct (shiftNameUp n ⌜ t ⌝) (→#shiftNameUp n {⌜ t ⌝} (CTerm.closed t))


differ-APPLY-upd : (name1 name2 : Name) (F f : Term)
                   → ¬Names F
                   → differ name1 name2 f (appUpd name1 F f) (appUpd name2 F f)
differ-APPLY-upd name1 name2 F f nnF =
  differ-APPLY _ _ _ _ (differ-refl name1 name2 f F nnF) differ-upd
{--  differ-LET
    _ _ _ _
    (differ-APPLY _ _ (upd name1 f) (upd name2 f) (differ-refl name1 name2 f F nnF) differ-upd)
    (differ-APPLY _ _ _ _ {!!} (differ-NUM 0))
--}




νtestM-NAT-shift : (cn : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F -- We require F to be pure
             → #¬Names f -- We require f to be pure
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → NATeq w (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)) (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f))
νtestM-NAT-shift cn exb gc i w F f nnF nnf ∈F ∈f =
  suc k , ack , ack
  where
    tM : Term
    tM = testM 0 (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ testM name ⌜ F ⌝ ⌜ f ⌝ from w to w1
    s1 = 1 , ≡pair (shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

    w2 : 𝕎·
    w2 = chooseT name w1 (NUM 0)

    cs : set0 name ⇓ AX from w1 to w2
    cs = 1 , refl

    e2 : w1 ⊑· w2
    e2 = ⇓from-to→⊑ {w1} {w2} cs

    -- we prove that in w2 name's value is 0
    gc0 : getT 0 name w2 ≡ just (NUM 0)
    gc0 = gc name w1 0 comp1

    g0 : ∀𝕎-get0-NUM w2 name
    g0 = cn name w1 0 comp1

    eqa : ∈Type i w2 #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→
            (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) w2 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w2 name f g0 (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))

    eqn : ∃𝕎 w2 (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#upd name f)))
    eqn = exb (equalInType-NAT→ i w2 (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa)

    wx2 : 𝕎·
    wx2 = fst eqn

    ex2 : w2 ⊑· wx2
    ex2 = fst (snd eqn)

    eqn' : NATeq wx2 (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
    eqn' = snd (snd eqn)

    cak : Σ ℕ (λ k → appUpd name ⌜ F ⌝ ⌜ f ⌝ ⇛ NUM k at wx2)
    cak = fst eqn' , fst (snd eqn')

    m : ℕ
    m = fst cak

    ca : Σ 𝕎· (λ w' → appUpd name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM m from wx2 to w')
    ca = ⇛→⇓from-to (snd cak)

    w3 : 𝕎·
    w3 = fst ca

    e3 : wx2 ⊑· w3
    e3 = ⇓from-to→⊑ {wx2} {w3} (snd ca)

    ca1 : Σ 𝕎· (λ w' → APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from w2 to w')
    ca1 = differNF⇓APPLY-upd gc ⌜ F ⌝  ⌜ f ⌝ (CTerm.closed f) name m wx2 w3 w2 nnF nnf
                             (⊑-compatible· (⊑-trans· e2 ex2) comp1) (⊑-compatible· e2 comp1)
                             (∀𝕎-mon ex2 g0) g0
                             (snd ca)

    w2x : 𝕎·
    w2x = fst ca1

    ca2 : APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ NUM m from w2 to w2x
    ca2 = snd ca1

    gt0 : Σ ℕ (λ k → getT 0 name w2x ≡ just (NUM k))
    gt0 = lower (g0 w2x (⇓from-to→⊑ {w2} {w2x} ca2))

    k : ℕ
    k = fst gt0

{--
    gk : get0 name ⇓ NUM k from w2x to w2x
    gk = 1 , step-APPLY-CS (NUM k) w2x 0 name (snd gt0)

    pbk : probeM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) from w2 to w2x
    pbk = ⇓-trans₂ (SEQ⇓₁ ca2) (⇓-trans₂ (SEQ-val⇓ w2x (NUM m) (SUC (get0 name)) tt) (⇓NUM→SUC⇓NUM gk))
--}

    ack : νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇛ NUM (suc k) at w
    ack w' e' = lift (⇓-from-to→⇓ {w'} {w3'} {νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)} {NUM (suc k)}
                                   (⇓-trans₂ {w'} {w1'} {w3'} {νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝)} {testM name' ⌜ F ⌝ ⌜ f ⌝} {NUM (suc k)}
                                             s1' (⇓-trans₂ {w1'} {w2'} {w3'} {testM name' ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name' ⌜ F ⌝ ⌜ f ⌝)} {NUM (suc k)}
                                                           (SEQ⇓₁ {w1'} {w2'} {set0 name'} {AX} {probeM name' ⌜ F ⌝ ⌜ f ⌝}  cs')
                                                           (⇓-trans₂ (SEQ-val⇓ w2' AX (probeM name' ⌜ F ⌝ ⌜ f ⌝) tt) pb'))))
      where
        name' : Name
        name' = newChoiceT w' tM

        w1' : 𝕎·
        w1' = startNewChoiceT Res⊤ w' tM

        e1' : w' ⊑· w1'
        e1' = startNewChoiceT⊏ Res⊤ w' tM

        comp1' : compatible· name' w1' Res⊤
        comp1' = startChoiceCompatible· Res⊤ w' name' (¬newChoiceT∈dom𝕎 w' tM)

        s1' : νtestM (shiftNameUp 0 ⌜ F ⌝) (shiftNameUp 0 ⌜ f ⌝) ⇓ testM name' ⌜ F ⌝ ⌜ f ⌝ from w' to w1'
        s1' = 1 , ≡pair (shiftNameDown-renn-shiftNameUp name' ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

        w2' : 𝕎·
        w2' = chooseT name' w1' (NUM 0)

        cs' : set0 name' ⇓ AX from w1' to w2'
        cs' = 1 , refl

        e2' : w1' ⊑· w2'
        e2' = ⇓from-to→⊑ {w1'} {w2'} cs'

        -- we prove that in w2 name's value is 0
        gc0' : getT 0 name' w2' ≡ just (NUM 0)
        gc0' = gc name' w1' 0 comp1'

        eqgt : getT 0 name w2 ≡ getT 0 name' w2'
        eqgt = trans gc0 (sym gc0')

        compat1 : compatible· name w2 Res⊤
        compat1 = ⊑-compatible· e2 comp1

        compat2 : compatible· name' w2' Res⊤
        compat2 = ⊑-compatible· e2' comp1'

        gt0n : ∀𝕎-get0-NUM w2 name
        gt0n w' e' = cn name w1 0 comp1 w' e'

        df : Σ 𝕎· (λ w3' → Σ Term (λ v' →
              appUpd name' ⌜ F ⌝ ⌜ f ⌝ ⇓ v' from w2' to w3' × differ name name' ⌜ f ⌝ (NUM m) v' × getT 0 name w2x ≡ getT 0 name' w3'))
        df = differ⇓from-to
               gc ⌜ f ⌝ (CTerm.closed f) nnf name name' w2 w2x w2'
               (appUpd name ⌜ F ⌝ ⌜ f ⌝)
               (appUpd name' ⌜ F ⌝ ⌜ f ⌝)
               (NUM m) tt compat1 compat2 gt0n
               (differ-APPLY-upd name name' ⌜ F ⌝ ⌜ f ⌝ nnF)
               eqgt ca2

        w3' : 𝕎·
        w3' = fst df

        v' : Term
        v' = fst (snd df)

        dfv' : differ name name' ⌜ f ⌝ (NUM m) v'
        dfv' = fst (snd (snd (snd df)))

        df0 : appUpd name' ⌜ F ⌝ ⌜ f ⌝ ⇓ v' from w2' to w3'
        df0 = fst (snd (snd df))

        df1 : appUpd name' ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM m from w2' to w3'
        df1 = ≡ᵣ→⇓from-to (differ-NUM→ dfv') df0

        pb' : probeM name' ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) from w2' to w3'
        pb' = ⇓-trans₂
                (SEQ⇓₁ df1)
                (⇓-trans₂
                  (SEQ-val⇓ w3' (NUM m) (SUC (get0 name')) tt)
                  (⇓NUM→SUC⇓NUM (1 , step-APPLY-CS (NUM k) w3' 0 name' (trans (sym (snd (snd (snd (snd df))))) (snd gt0)))))



νtestM-NAT : (cn : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
             (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F -- We require F to be pure
             → #¬Names f -- We require f to be pure
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → NATeq w (#νtestM F f) (#νtestM F f)
νtestM-NAT cn exb gc i w F f nnF nnf ∈F ∈f = concl h
  where
    h : NATeq w (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)) (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f))
    h = νtestM-NAT-shift cn exb gc i w F f nnF nnf ∈F ∈f

    concl : NATeq w (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)) (#νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f))
            → NATeq w (#νtestM F f) (#νtestM F f)
    concl rewrite ¬Names→shiftNameUp≡ ⌜ F ⌝ 0 nnF | ¬Names→shiftNameUp≡ ⌜ f ⌝ 0 nnf = λ x → x



testM-NAT : (cn : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (F f : CTerm)
            → #¬Names F
            → #¬Names f
            → ∈Type i w #BAIRE→NAT F
            → ∈Type i w #BAIRE f
            → ∈Type i w #NAT (#νtestM F f)
testM-NAT cn exb gc i w F f nnF nnf ∈F ∈f =
  →equalInType-NAT i w (#νtestM F f) (#νtestM F f) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → NATeq w' (#νtestM F f) (#νtestM F f))
    aw w' e' = νtestM-NAT cn exb gc i w' F f nnF nnf (equalInType-mon ∈F w' e') (equalInType-mon ∈f w' e')



#contBody : (F f : CTerm) → CTerm
#contBody F f = ct (contBody ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # contBody ⌜ F ⌝ ⌜ f ⌝
    c rewrite CTerm.closed f
            | #shiftUp 0 f
            | #shiftUp 0 F
            | CTerm.closed F
            | CTerm.closed f
            | #shiftUp 1 f
            | #shiftUp 1 F
            | CTerm.closed F
            | CTerm.closed f = refl


#[0]BAIRE : CTerm0
#[0]BAIRE = ct0 BAIRE c
  where
    c : #[ [ 0 ] ] BAIRE
    c = refl


#[1]BAIRE : CTerm1
#[1]BAIRE = ct1 BAIRE c
  where
    c : #[ 0 ∷ [ 1 ] ] BAIRE
    c = refl



#[1]FUN : CTerm1 → CTerm1 → CTerm1
#[1]FUN a b = ct1 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[1]EQ : CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]EQ a b c = ct1 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ [ 1 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b))
                        (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ [ 1 ]} (CTerm1.closed c))))


--fvars-NATn : (n : Term) → fvars (NATn n) ≡ fvars n
--fvars-NATn n = ?


#contBody≡ : (F f : CTerm)
            → #contBody F f
               ≡ #SUM #NAT
                      (#[0]PI #[0]BAIRE
                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
#contBody≡ F f = CTerm≡ refl



sub0-contBodyPI : (F f a : CTerm)
                  → sub0 a (#[0]PI #[0]BAIRE
                                    (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                             (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                      (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
                    ≡ #PI #BAIRE
                          (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                   (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ a ⌟))
                                            (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
sub0-contBodyPI F f a
  rewrite CTerm→CTerm1→Term f
    = CTerm≡ (≡PI refl (≡PI refl (≡PI e1 e2)))
  where
    e1 : EQ (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) (shiftUp 0 ⌜ f ⌝)))
            (VAR 1)
            (PI (SET NAT (LT (VAR 0) (shiftDown 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))))))) NAT)
         ≡ EQ (shiftUp 0 ⌜ f ⌝) (VAR 1) (PI (SET NAT (LT (VAR 0) (shiftUp 1 (shiftUp 0 ⌜ a ⌝)))) NAT)
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftUp 0 f
             | #subv 2 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 2 a | #shiftDown 3 a | #shiftDown 2 f | #shiftDown 1 f = refl

    e2 : EQ (APPLY (shiftDown 3 (subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (shiftDown 3 (subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))) (shiftUp 1 (shiftUp 0 ⌜ f ⌝)))))
            (APPLY (shiftDown 3 (subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (VAR 2))
            NAT
         ≡ EQ (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (shiftUp 1 (shiftUp 0 ⌜ f ⌝))) (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (VAR 2)) NAT
    e2 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 F | #shiftUp 0 f
             | #shiftUp 1 F | #shiftUp 1 f
             | #subv 3 ⌜ a ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #subv 3 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 3 F | #shiftDown 3 f = refl


sub0-contBodyPI-PI : (F f a g : CTerm)
                    → sub0 g (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                       (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ a ⌟))
                                                (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
                       ≡ #FUN (#FFDEFS #BAIRE g) (#FUN (#EQ f g (#BAIREn a)) (#EQ (#APPLY F f) (#APPLY F g) #NAT))
sub0-contBodyPI-PI F f a g
  rewrite CTerm→CTerm1→Term f =
  CTerm≡ (≡PI e0 (≡PI e1 e2))
  where
    e0 : FFDEFS BAIRE (shiftDown 0 (shiftUp 0 ⌜ g ⌝))
         ≡ FFDEFS BAIRE ⌜ g ⌝
    e0 rewrite #shiftUp 0 g | #shiftDown 0 g = refl

    e1 : EQ (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)))
            (shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)))
            (PI (SET NAT (LT (VAR 0) (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ a ⌝)))))) NAT)
         ≡ EQ (shiftUp 0 ⌜ f ⌝) (shiftUp 0 ⌜ g ⌝) (PI (SET NAT (LT (VAR 0) (shiftUp 1 (shiftUp 0 ⌜ a ⌝)))) NAT)
    e1 rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 a | #shiftUp 1 a | #shiftUp 0 f
             | #subv 1 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #subv 2 ⌜ g ⌝ ⌜ a ⌝ (CTerm.closed a)
             | #shiftDown 1 f | #shiftDown 2 a | #shiftDown 1 g = refl --refl

    e2 : EQ (APPLY (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ f ⌝)))))
            (APPLY (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)))))
            NAT
         ≡ EQ (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (shiftUp 1 (shiftUp 0 ⌜ f ⌝))) (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (shiftUp 1 (shiftUp 0 ⌜ g ⌝))) NAT
    e2 rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 F | #shiftUp 0 f | #shiftUp 0 g
             | #shiftUp 1 F | #shiftUp 1 f | #shiftUp 1 g
             | #subv 2 ⌜ g ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #subv 2 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 2 F | #shiftDown 2 f | #shiftDown 2 g = refl



sub0-NATn-body : (a n : CTerm) → sub0 a (#[0]LT #[0]VAR ⌞ n ⌟) ≡ #LT a n
sub0-NATn-body a n rewrite CTerm→CTerm0→Term n = CTerm≡ e
  where
    e : LT (shiftDown 0 (shiftUp 0 ⌜ a ⌝)) (shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ n ⌝))
        ≡ LT (CTerm.cTerm a) ⌜ n ⌝
    e rewrite #shiftUp 0 a
            | #subv 0 ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 n | #shiftDown 0 a = refl



→equalTypesNATn : (i : ℕ) (w : 𝕎·) (a₁ a₂ : CTerm)
                   → equalInType i w #NAT a₁ a₂
                   → equalTypes i w (#NATn a₁) (#NATn a₂)
→equalTypesNATn i w a₁ a₂ ea =
  ≡CTerm→eqTypes
    (sym (≡NATn a₁))
    (sym (≡NATn a₂))
    (eqTypesSET← (λ w' e' → eqTypesNAT) aw1)
  where
    aw2 : ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' #NAT b₁ b₂
                       → equalTypes i w' (#LT b₁ a₁) (#LT b₂ a₂))
    aw2 w1 e1 b₁ b₂ eb = →equalTypesLT eb (equalInType-mon ea w1 e1)

    aw1 : ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' #NAT b₁ b₂
                       → equalTypes i w' (sub0 b₁ (#[0]LT #[0]VAR ⌞ a₁ ⌟)) (sub0 b₂ (#[0]LT #[0]VAR ⌞ a₂ ⌟)))
    aw1 w1 e1 b₁ b₂ eb = ≡CTerm→eqTypes (sym (sub0-NATn-body b₁ a₁)) (sym (sub0-NATn-body b₂ a₂)) (aw2 w1 e1 b₁ b₂ eb)



→equalTypesBAIREn : (i : ℕ) (w : 𝕎·) (a₁ a₂ : CTerm)
                     → equalInType i w #NAT a₁ a₂
                     → equalTypes i w (#BAIREn a₁) (#BAIREn a₂)
→equalTypesBAIREn i w a₁ a₂ ea =
  ≡CTerm→eqTypes
    (sym (≡BAIREn a₁))
    (sym (≡BAIREn a₂))
    (eqTypesFUN← (→equalTypesNATn i w a₁ a₂ ea) eqTypesNAT)




∈NATn→∈NAT : {i : ℕ} {w : 𝕎·} {a b n : CTerm}
              → equalInType i w #NAT n n
              → equalInType i w (#NATn n) a b
              → equalInType i w #NAT a b
∈NATn→∈NAT {i} {w} {a} {b} {n} en ea =
  →equalInType-NAT i w a b (Mod.□-idem M (Mod.∀𝕎-□Func M aw1 eb2))
  where
    eb1 : equalInType i w (#SET #NAT (#[0]LT #[0]VAR ⌞ n ⌟)) a b
    eb1 = ≡CTerm→equalInType (≡NATn n) ea

    eb2 : □· w (λ w' _ → SETeq (equalInType i w' #NAT) (λ x y ea → equalInType i w' (sub0 x (#[0]LT #[0]VAR ⌞ n ⌟))) a b)
    eb2 = equalInType-SET→ eb1

    aw1 : ∀𝕎 w (λ w' e' → SETeq (equalInType i w' #NAT) (λ x y ea₁ → equalInType i w' (sub0 x (#[0]LT #[0]VAR (CTerm→CTerm0 n)))) a b
                        → □· w' (↑wPred' (λ w'' _ → NATeq w'' a b) e'))
    aw1 w1 e1 (x , ex , ey) = Mod.∀𝕎-□Func M (λ w2 e2 s z → s) (equalInType-NAT→ i w1 a b ex)


∈BAIRE→∈BAIREn : {i : ℕ} {w : 𝕎·} {f g n : CTerm}
                  → equalInType i w #NAT n n
                  → equalInType i w #BAIRE f g
                  → equalInType i w (#BAIREn n) f g
∈BAIRE→∈BAIREn {i} {w} {f} {g} {n} en ef =
  ≡CTerm→equalInType
    (sym (≡BAIREn n))
    (equalInType-FUN (→equalTypesNATn i w n n en)
                     eqTypesNAT
                     aw)
  where
    ef1 : equalInType i w (#FUN #NAT #NAT) f g
    ef1 = ≡CTerm→equalInType #BAIRE≡ ef

    ef2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂ → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    ef2 = equalInType-FUN→ ef1

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn n) a₁ a₂
                      → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    aw w1 e1 a₁ a₂ ea = ef2 w1 e1 a₁ a₂ (∈NATn→∈NAT (equalInType-mon en w1 e1) ea)



∈BAIRE→NAT→ : {i : ℕ} {w : 𝕎·} {F₁ F₂ f₁ f₂ : CTerm}
                → equalInType i w #BAIRE→NAT F₁ F₂
                → equalInType i w #BAIRE f₁ f₂
                → equalInType i w #NAT (#APPLY F₁ f₁) (#APPLY F₂ f₂)
∈BAIRE→NAT→ {i} {w} {F₁} {F₂} {f₁} {f₂} ∈F ∈f =
  equalInType-FUN→
    {i} {w} {#BAIRE} {#NAT} {F₁} {F₂} ∈F w (⊑-refl· _) f₁ f₂
    ∈f



equalTypes-contBodyPI : (i : ℕ) (w : 𝕎·) (F₁ F₂ f₁ f₂ : CTerm)
                        → equalInType i w #BAIRE→NAT F₁ F₂
                        → equalInType i w #BAIRE f₁ f₂
                        → ∀𝕎 w (λ w' e →
                             (a₁ a₂ : CTerm)
                             → equalInType i w' #NAT a₁ a₂
                             → equalTypes i w'
                                 (sub0 a₁ (#[0]PI #[0]BAIRE
                                          (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                   (#[1]FUN (#[1]EQ ⌞ f₁ ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                            (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ ⌞ f₁ ⌟) (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) #[1]NAT)))))
                                 (sub0 a₂ (#[0]PI #[0]BAIRE
                                          (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                   (#[1]FUN (#[1]EQ ⌞ f₂ ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                            (#[1]EQ (#[1]APPLY ⌞ F₂ ⌟ ⌞ f₂ ⌟) (#[1]APPLY ⌞ F₂ ⌟ #[1]VAR0) #[1]NAT))))))
equalTypes-contBodyPI i w F₁ F₂ f₁ f₂ ∈F ∈f w1 e1 a₁ a₂ ea =
  ≡CTerm→eqTypes (sym (sub0-contBodyPI F₁ f₁ a₁)) (sym (sub0-contBodyPI F₂ f₂ a₂)) ea1
  where
    ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                         → equalTypes i w2
                               (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f₁ g₁ (#BAIREn a₁)) (#EQ (#APPLY F₁ f₁) (#APPLY F₁ g₁) #NAT)))
                               (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f₂ g₂ (#BAIREn a₂)) (#EQ (#APPLY F₂ f₂) (#APPLY F₂ g₂) #NAT))))
    ea2 w2 e2 g₁ g₂ eg =
      eqTypesFUN←
        (eqTypesFFDEFS← eqTypesBAIRE eg)
        (eqTypesFUN←
          (eqTypesEQ← (→equalTypesBAIREn i w2 a₁ a₂ (equalInType-mon ea w2 e2))
                      (∈BAIRE→∈BAIREn (equalInType-refl (equalInType-mon ea w2 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                      (∈BAIRE→∈BAIREn (equalInType-refl (equalInType-mon ea w2 e2)) eg))
          (eqTypesEQ← eqTypesNAT
                      (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                      (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

    ea1 : equalTypes i w1
            (#PI #BAIRE
                 (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                          (#[0]FUN (#[0]EQ ⌞ f₁ ⌟ #[0]VAR (#[0]BAIREn ⌞ a₁ ⌟))
                                   (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ ⌞ f₁ ⌟) (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) #[0]NAT))))
            (#PI #BAIRE
                 (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                          (#[0]FUN (#[0]EQ ⌞ f₂ ⌟ #[0]VAR (#[0]BAIREn ⌞ a₂ ⌟))
                                   (#[0]EQ (#[0]APPLY ⌞ F₂ ⌟ ⌞ f₂ ⌟) (#[0]APPLY ⌞ F₂ ⌟ #[0]VAR) #[0]NAT))))
    ea1 = eqTypesPI← (λ w' _ → eqTypesBAIRE)
                      (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contBodyPI-PI F₁ f₁ a₁ g₁)) (sym (sub0-contBodyPI-PI F₂ f₂ a₂ g₂)) (ea2 w2 e2 g₁ g₂ eg))




equalTypes-contBody : (i : ℕ) (w : 𝕎·) (F₁ F₂ f₁ f₂ : CTerm)
                      → equalInType i w #BAIRE→NAT F₁ F₂
                      → equalInType i w #BAIRE f₁ f₂
                      → equalTypes i w (#contBody F₁ f₁) (#contBody F₂ f₂)
equalTypes-contBody i w F₁ F₂ f₁ f₂ ∈F ∈f =
  ≡CTerm→eqTypes
    (sym (#contBody≡ F₁ f₁))
    (sym (#contBody≡ F₂ f₂))
    (eqTypesSUM←
      (λ w' e' → eqTypesNAT)
      (equalTypes-contBodyPI i w F₁ F₂ f₁ f₂ ∈F ∈f))




equalInType-BAIREn-BAIRE-trans : {i : ℕ} {w : 𝕎·} {a b c n : CTerm}
                                 → equalInType i w #BAIRE b c
                                 → equalInType i w (#BAIREn n) a b
                                 → equalInType i w #NAT n n
                                 → equalInType i w (#BAIREn n) a c
equalInType-BAIREn-BAIRE-trans {i} {w} {a} {b} {c} {n} h1 h2 h3 =
  equalInType-trans h2 h4
  where
    h4 : equalInType i w (#BAIREn n) b c
    h4 = ∈BAIRE→∈BAIREn h3 h1



{--
data apps (f : Term) : ℕ → Term → Set where
  appsF : apps f n (APPLY f (NUM n))
  appsAPP : (a b : Term) (n : ℕ) → ¬ a ≡ f → apps f n a → apps f n (APPLY a b)
  appsIFLT : (a b c d : Term) (n : ℕ) → apps f n a
--}


--steps K (APPLY F f , w) ≡ (NUM n , w)
--→ Σ ℕ (λ m → #νtestM F f ≡ NUM m × )



¬Names→⇓→⇛ : (w w' : 𝕎·) (t u : Term)
               → ¬Names t
               → t ⇓ u at w
               → t ⇛ u at w
¬Names→⇓→⇛ w w' t u nnt comp w1 e1 =
  lift (⇓-from-to→⇓ {w1} {w1} (fst (snd h) , fst (¬Names→steps (fst (snd h)) w (fst h) w1 t u nnt (snd (snd h)))))
  where
    h : Σ 𝕎· (λ w' → t ⇓ u from w to w')
    h = ⇓→from-to comp


#¬Names-APPLY : {a b : CTerm} → #¬Names a → #¬Names b → #¬Names (#APPLY a b)
#¬Names-APPLY {a} {b} nna nnb rewrite nna | nnb = refl



equalInType-NATn→ : {i : ℕ} {w : 𝕎·} {n : ℕ} {t a b : CTerm}
                     → t #⇛ #NUM n at w
                     → equalInType i w (#NATn t) a b
                     → □· w (λ w' _ → Σ ℕ (λ k → a #⇛ #NUM k at w' × b #⇛ #NUM k at w' × k < n))
equalInType-NATn→ {i} {w} {n} {t} {a} {b} compt eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw eqi1)
  where
    eqi1 : □· w (λ w' _ → SETeq (equalInType i w' #NAT) (λ a b ea → equalInType i w' (sub0 a (#[0]LT #[0]VAR ⌞ t ⌟))) a b)
    eqi1 = equalInType-SET→ {i} {w} {#NAT} {#[0]LT #[0]VAR ⌞ t ⌟} {a} {b} (≡CTerm→equalInType (≡NATn t) eqi)

    aw : ∀𝕎 w (λ w' e' → SETeq (equalInType i w' #NAT) (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]LT #[0]VAR ⌞ t ⌟))) a b
                        → □· w' (↑wPred' (λ w'' _ → Σ ℕ (λ k → a #⇛ #NUM k at w'' × b #⇛ #NUM k at w'' × k < n)) e'))
    aw w1 e1 (k0 , eqk , eqj) = Mod.∀𝕎-□Func M aw1 eqk1
      where
        eqj1 : equalInType i w1 (#LT a t) k0 k0
        eqj1 = ≡CTerm→equalInType (sub0-NATn-body a t) eqj

        eqk1 : □· w1 (λ w' _ → NATeq w' a b)
        eqk1 = equalInType-NAT→ i w1 a b eqk

        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a b
                             → ↑wPred' (λ w'' _ → Σ ℕ (λ k₁ → a #⇛ #NUM k₁ at w'' × b #⇛ #NUM k₁ at w'' × k₁ < n)) e1 w' e')
        aw1 w2 e2 (k , comp1 , comp2) z = k , comp1 , comp2 , equalInType-LT-⇛NUM→ {i} {w2} {a} {t} comp1 (∀𝕎-mon (⊑-trans· e1 e2) compt) (equalInType-mon eqj1 w2 e2)



#⇛NUM∈NAT : {i : ℕ} {w : 𝕎·} {a : CTerm} {n : ℕ}
             → a #⇛ #NUM n at w
             → ∈Type i w #NAT a
#⇛NUM∈NAT {i} {w} {a} {n} comp = →equalInType-NAT i w a a (Mod.∀𝕎-□ M (λ w1 e1 → n , ∀𝕎-mon e1 comp , ∀𝕎-mon e1 comp))



→equalInTypeLT : {i : ℕ} {w : 𝕎·} {a b u v : CTerm} {n m : ℕ}
                  → n < m
                  → a #⇛ #NUM n at w
                  → b #⇛ #NUM m at w
                  → equalInType i w (#LT a b) u v
→equalInTypeLT {i} {w} {a} {b} {u} {v} {n} {m} ltn c1 c2 =
  EQTLT a a b b (#compAllRefl (#LT a b) w) (#compAllRefl (#LT a b) w) (n , c1 , c1) (m , c2 , c2) ,
  Mod.∀𝕎-□ M (λ w1 e1 → lift (n , m , lower (c1 w1 e1) , lower (c2 w1 e1) , ltn))



→equalInType-NATn : {i : ℕ} {w : 𝕎·} {n : ℕ} {t a b : CTerm}
                     → t #⇛ #NUM n at w
                     → □· w (λ w' _ → Σ ℕ (λ k → a #⇛ #NUM k at w' × b #⇛ #NUM k at w' × k < n))
                     → equalInType i w (#NATn t) a b
→equalInType-NATn {i} {w} {n} {t} {a} {b} compt eqi =
  ≡CTerm→equalInType
    (sym (≡NATn t))
    (equalInType-SET
      (λ w' _ → eqTypesNAT)
      (λ w' e' a₁ a₂ eqa → ≡CTerm→eqTypes (sym (sub0-NATn-body a₁ t)) (sym (sub0-NATn-body a₂ t)) (→equalTypesLT eqa (#⇛NUM∈NAT (∀𝕎-mon e' compt))))
      (λ w' e' → →equalInType-NAT i w' a b (Mod.∀𝕎-□Func M (λ w'' e'' (k , c1 , c2 , ltn) → k , c1 , c2) (Mod.↑□ M eqi e')))
      (Mod.∀𝕎-□Func M aw eqi))
  where
    aw : ∀𝕎 w (λ w' e' → Σ ℕ (λ k → a #⇛ #NUM k at w' × b #⇛ #NUM k at w' × k < n)
                        → Σ CTerm (∈Type i w' (sub0 a (#[0]LT #[0]VAR ⌞ t ⌟))))
    aw w1 e1 (k , c1 , c2 , ltn) = #AX , ≡CTerm→equalInType (sym (sub0-NATn-body a t)) (→equalInTypeLT {i} {w1} {a} {t} ltn c1 (∀𝕎-mon e1 compt))



NATeq→⇛ : {w : 𝕎·} {t : CTerm} {n : ℕ}
            → NATeq w t (#NUM n)
            → t #⇛ #NUM n at w
NATeq→⇛ {w} {t} {n} (k , c1 , c2) rewrite #NUMinj (#compAllVal {#NUM n} {#NUM k} {w} c2 tt) = c1



force : Term → Term
force f = LAMBDA (LET (VAR 0) (APPLY f (VAR 0)))


#force : CTerm → CTerm
#force f = ct (force ⌜ f ⌝) c
  where
    c : # force ⌜ f ⌝
    c rewrite CTerm.closed f = refl


sub-force-body : (a f : CTerm) → sub ⌜ a ⌝ (LET (VAR 0) (APPLY ⌜ f ⌝ (VAR 0))) ≡ LET ⌜ a ⌝ (APPLY ⌜ f ⌝ (VAR 0))
sub-force-body a f
  rewrite #shiftUp 0 a | #shiftUp 0 a
        | #subv 1 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 0 a | #shiftDown 1 f = refl



sub-force-body-let : (a f : CTerm) → sub ⌜ a ⌝ (APPLY ⌜ f ⌝ (VAR 0)) ≡ APPLY ⌜ f ⌝ ⌜ a ⌝
sub-force-body-let a f
  rewrite #shiftUp 0 a | #subv 0 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f) | #shiftDown 0 a | #shiftDown 0 f = refl


≡L→⇓ : {w : 𝕎·} {a b c : Term} → a ≡ b → a ⇓ c at w → b ⇓ c at w
≡L→⇓ {w} {a} {b} {c} e comp rewrite e = comp



≡L→⇓-from-to : {w1 w2 : 𝕎·} {a b c : Term} → a ≡ b → a ⇓ c from w1 to w2 → b ⇓ c from w1 to w2
≡L→⇓-from-to {w1} {w2} {a} {b} {c} e comp rewrite e = comp



Σ⇓-from-to→⇓ : {w : 𝕎·} {a b : Term}
              → Σ 𝕎· (λ w' → a ⇓ b from w to w')
              → a ⇓ b at w
Σ⇓-from-to→⇓ {w} {a} {b} (w' , comp) = ⇓-from-to→⇓ comp



#APPLY-force : {w : 𝕎·} {f a : CTerm} {k : ℕ}
               → a #⇛ #NUM k at w
               → #APPLY (#force f) a #⇛ #APPLY f (#NUM k) at w
#APPLY-force {w} {f} {a} {k} comp w1 e1 =
  lift (step-⇓-trans refl (≡L→⇓ (sym (sub-force-body a f))
                                 (Σ⇓-from-to→⇓ (fst ca , ⇓-trans₂ {w1} {fst ca} {fst ca}
                                                                  (LET⇓ (APPLY ⌜ f ⌝ (VAR 0)) (snd ca))
                                                                  (⇓-trans₂ {fst ca} {fst ca} {fst ca}
                                                                            (LET-val⇓ (fst ca) (NUM k) (APPLY ⌜ f ⌝ (VAR 0)) tt)
                                                                            (≡L→⇓-from-to (sym (sub-force-body-let (ct (NUM k) refl) f))
                                                                                          (⇓from-to-refl (APPLY ⌜ f ⌝ (NUM k)) (fst ca))))))))
  where
    ca : Σ 𝕎· (λ w2 → ⌜ a ⌝ ⇓ NUM k from w1 to w2)
    ca = ⇓→from-to (lower (comp w1 e1))


⇛NUM→equalInType-NAT : {i : ℕ} {w : 𝕎·} {a : CTerm} {k : ℕ}
                        → a #⇛ #NUM k at w
                        → equalInType i w #NAT a (#NUM k)
⇛NUM→equalInType-NAT {i} {w} {a} {k} comp = →equalInType-NAT i w a (#NUM k) (Mod.∀𝕎-□ M (λ w1 e1 → (k , ∀𝕎-mon e1 comp , #compAllRefl (#NUM k) w1)))


equalInType-force : {i : ℕ} {w : 𝕎·} {f : CTerm}
                    → ∈Type i w #BAIRE f
                    → equalInType i w #BAIRE f (#force f)
equalInType-force {i} {w} {f} eqi =
  equalInType-FUN
    eqTypesNAT
    eqTypesNAT
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                        → equalInType i w' #NAT (#APPLY f a₁) (#APPLY (#force f) a₂))
    aw1 w1 e1 a₁ a₂ ea =
      equalInType-local (Mod.∀𝕎-□Func M aw2 (equalInType-NAT→ i w1 a₁ a₂ ea)) --→equalInType-NAT i w1 (#APPLY f a₁) (#APPLY (#force f) a₂) {!!} --(Mod.∀𝕎-□Func M aw2 (equalInType-NAT→ i w1 a₁ a₂ ea))
      where
        aw2 : ∀𝕎 w1 (λ w' e' →  NATeq w' a₁ a₂ → equalInType i w' #NAT (#APPLY f a₁) (#APPLY (#force f) a₂))
        aw2 w2 e2 (k , c1 , c2) = →equalInType-NAT i w2 (#APPLY f a₁) (#APPLY (#force f) a₂) (Mod.∀𝕎-□Func M aw3 (equalInType-NAT→ i w2 (#APPLY f a₁) (#APPLY f (#NUM k)) eqi1))
          where
            eqi1 : equalInType i w2 #NAT (#APPLY f a₁) (#APPLY f (#NUM k))
            eqi1 = equalInType-FUN→ eqi w2 (⊑-trans· e1 e2) a₁ (#NUM k) (⇛NUM→equalInType-NAT c1)

            aw3 : ∀𝕎 w2 (λ w' e' → NATeq w' (#APPLY f a₁) (#APPLY f (#NUM k)) → NATeq w' (#APPLY f a₁) (#APPLY (#force f) a₂))
            aw3 w3 e3 (z , comp1 , comp2) = z , comp1 , ⇛-trans (#APPLY-force {w3} {f} {a₂} (∀𝕎-mon e3 c2)) comp2



equalInType-APPLY-force : {i : ℕ} {w : 𝕎·} {F f : CTerm}
                          → ∈Type i w #BAIRE→NAT F
                          → ∈Type i w #BAIRE f
                          → equalInType i w #NAT (#APPLY F f) (#APPLY F (#force f))
equalInType-APPLY-force {i} {w} {F} {f} eqF eqf = ∈BAIRE→NAT→ eqF (equalInType-force eqf)


#¬Names-force : {a : CTerm} → #¬Names a → #¬Names (#force a)
#¬Names-force {a} nna rewrite nna = refl

\end{code}
