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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
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
open import compatible
open import progress
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import mod
open import encode


module mp_prop {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
               (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
               (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
               (N : NewChoice {L} W C K G)
               (EC : Encode)
               (V : ChoiceVal W C K G X N EC)
               (F : Freeze {L} W C K P G N)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
               (CB : ChoiceBar W M C K P G X N EC V F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (<Type ; <Type1 ; <TypeBAR)
open import ind3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-ind)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (#subv)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (lowerVars-fvars-[0,1,2,3])

open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--  using (equalInType→eqInType ; eqInType→equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-LIFT2 ; equalInType→equalTypes-aux ; equalInType-FUN→ ; ≡CTerm→equalInType ; eqTypesSQUASH← ;
         eqTypesSUM← ; isTypeNAT! ; eqTypesNEG← ; →≡equalTypes ; eqTypesPI← ; eqTypesFUN← ; eqTypesUniv ;
         equalInType-NEG ; eqTypesUNION← ; equalInType-SQUASH→ ; equalInType-SUM→ ; equalInType-refl ;
         equalInType-LIFT→ ; equalInType-PI→ ; equalInType-PI ; equalInType-NEG→ ; equalInType-SUM ; equalInType-mon ;
         equalInType-LIFT← ; NUM-equalInType-NAT! ; equalTypes→equalInType-UNIV ; equalInType-local ; equalInType-EQ→ ;
         equalInType-NAT!→ ; ¬equalInType-FALSE)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-SQUASH ; →equalInType-CS-NAT!→T ; equalTerms-pres-#⇛-left-rev ; equalTypes-#⇛-left-right-rev ;
         →equalInType-TRUE ; →equalInType-UNION)

open import pure2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (∈NAT!-change-level)

--open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using ()

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
  using (#[0]Typeℂ₀₁ ; Typeℂ₀₁· ; □·-choice·)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
  using (#Σchoice ; #Σchoice≡ ; ¬∀𝕎¬equalInType-#Σchoice ; sub0-#Σchoice-body≡)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
  using (Resℂ ; →equalInType-APPLY-CS-Typeℂ₀₁·)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)




NAT!→U : ℕ → Term
NAT!→U i = FUN NAT! (UNIV i)


#NAT!→U : ℕ → CTerm
#NAT!→U i = ct (NAT!→U i) refl


#NAT!→U≡ : (i : ℕ) → #NAT!→U i ≡ #FUN #NAT! (#UNIV i)
#NAT!→U≡ i = CTerm≡ refl


#[0]LIFT : CTerm0 → CTerm0
#[0]LIFT a = ct0 (LIFT ⌜ a ⌝) (CTerm0.closed a)


#[1]LIFT : CTerm1 → CTerm1
#[1]LIFT a = ct1 (LIFT ⌜ a ⌝) (CTerm1.closed a)


#[2]LIFT : CTerm2 → CTerm2
#[2]LIFT a = ct2 (LIFT ⌜ a ⌝) (CTerm2.closed a)


fvars-CTerm1 : (a : CTerm1) → fvars ⌜ a ⌝ ⊆ 0 ∷ [ 1 ]
fvars-CTerm1 a = ⊆?→⊆ (CTerm1.closed a)


fvars-CTerm2 : (a : CTerm2) → fvars ⌜ a ⌝ ⊆ 0 ∷ 1 ∷ [ 2 ]
fvars-CTerm2 a = ⊆?→⊆ (CTerm2.closed a)


#[1]SQUASH : CTerm1 → CTerm1
#[1]SQUASH a = ct1 (SQUASH ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SQUASH ⌜ a ⌝
    c rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ = ⊆→⊆? {lowerVars (Data.List.map suc (fvars ⌜ a ⌝))} {0 ∷ [ 1 ]} s
      where
        s : lowerVars (Data.List.map suc (fvars ⌜ a ⌝)) ⊆ 0 ∷ [ 1 ]
        s {z} i = w
          where
            x : suc z ∈ Data.List.map suc (fvars ⌜ a ⌝)
            x = ∈lowerVars→ z (Data.List.map suc (fvars ⌜ a ⌝)) i

            y : Var
            y = fst (∈-map⁻ suc x)

            j : y ∈ fvars ⌜ a ⌝
            j = fst (snd (∈-map⁻ suc x))

            e : z ≡ y
            e = suc-injective (snd (snd (∈-map⁻ suc x)))

            w : z ∈ 0 ∷ [ 1 ]
            w rewrite e = fvars-CTerm1 a j


#[2]SQUASH : CTerm2 → CTerm2
#[2]SQUASH a = ct2 (SQUASH ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] SQUASH ⌜ a ⌝
    c rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ = ⊆→⊆? {lowerVars (Data.List.map suc (fvars ⌜ a ⌝))} {0 ∷ 1 ∷ [ 2 ]} s
      where
        s : lowerVars (Data.List.map suc (fvars ⌜ a ⌝)) ⊆ 0 ∷ 1 ∷ [ 2 ]
        s {z} i = w
          where
            x : suc z ∈ Data.List.map suc (fvars ⌜ a ⌝)
            x = ∈lowerVars→ z (Data.List.map suc (fvars ⌜ a ⌝)) i

            y : Var
            y = fst (∈-map⁻ suc x)

            j : y ∈ fvars ⌜ a ⌝
            j = fst (snd (∈-map⁻ suc x))

            e : z ≡ y
            e = suc-injective (snd (snd (∈-map⁻ suc x)))

            w : z ∈ 0 ∷ 1 ∷ [ 2 ]
            w rewrite e = fvars-CTerm2 a j


#[1]UNION : CTerm1 → CTerm1 → CTerm1
#[1]UNION a b = ct1 (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] UNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


↑APPLY : Term → Term → Term
↑APPLY f a = LIFT (APPLY f a)


#↑APPLY : CTerm → CTerm → CTerm
#↑APPLY f a = #LIFT (#APPLY f a)


#[0]↑APPLY : CTerm0 → CTerm0 → CTerm0
#[0]↑APPLY f a = #[0]LIFT (#[0]APPLY f a)


#[1]↑APPLY : CTerm1 → CTerm1 → CTerm1
#[1]↑APPLY f a = #[1]LIFT (#[1]APPLY f a)


OR : Term → Term → Term
OR a b = SQUASH (UNION a b)


#OR : CTerm → CTerm → CTerm
#OR a b = #SQUASH (#UNION a b)


#[0]OR : CTerm0 → CTerm0 → CTerm0
#[0]OR a b = #[0]SQUASH (#[0]UNION a b)


#[1]OR : CTerm1 → CTerm1 → CTerm1
#[1]OR a b = #[1]SQUASH (#[1]UNION a b)


DECℕ : Term → Term
DECℕ F = PI NAT! (OR (↑APPLY (shiftUp 0 F) (VAR 0)) (NEG (↑APPLY (shiftUp 0 F) (VAR 0))))


-- π (F : ℕ → 𝕌ᵢ). (Π (n : ℕ). F n ∨ ¬ F n) → ¬(Π (n : ℕ). ¬(F n)) → ||Σ (n : ℕ). F n||
MPℙ : ℕ → Term
MPℙ i =
  PI (NAT!→U i)
     (FUN (DECℕ (VAR 0))
          (FUN (NEG (NEG (SQUASH (SUM NAT! (↑APPLY (VAR 1) (VAR 0))))))
               (SQUASH (SUM NAT! (↑APPLY (VAR 1) (VAR 0))))))


#[0]MPℙ-right : CTerm0
#[0]MPℙ-right = #[0]SQUASH (#[0]SUM #[0]NAT! (#[1]LIFT (#[1]APPLY #[1]VAR1 #[1]VAR0)))


#[0]MPℙ-left : CTerm0
#[0]MPℙ-left = #[0]NEG (#[0]NEG #[0]MPℙ-right)


#[1]SUM : CTerm1 → CTerm2 → CTerm1
#[1]SUM a b = ct1 (SUM ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUM ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[1]PI : CTerm1 → CTerm2 → CTerm1
#[1]PI a b = ct1 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                      (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[2]PI : CTerm2 → CTerm3 → CTerm2
#[2]PI a b = ct2 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ [ 2 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                      (lowerVars-fvars-[0,1,2,3] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm3.closed b))))


#[3]EQ : CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]EQ a b c = ct3 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
                 (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                       (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b))
                             (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed c))))


#[1]BOOL : CTerm1
#[1]BOOL = ct1 BOOL refl


#[2]BOOL : CTerm2
#[2]BOOL = ct2 BOOL refl


#[3]BOOL : CTerm3
#[3]BOOL = ct3 BOOL refl


#[3]FUN : CTerm3 → CTerm3 → CTerm3
#[3]FUN a b = ct3 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                     (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


#[0]DECℕ : CTerm0
#[0]DECℕ = #[0]PI #[0]NAT! (#[1]OR (#[1]↑APPLY #[1]VAR1 #[1]VAR0)
                                   (#[1]NEG (#[1]↑APPLY #[1]VAR1 #[1]VAR0)))


#DECℕ : CTerm → CTerm
#DECℕ f = #PI #NAT! (#[0]OR (#[0]↑APPLY ⌞ f ⌟ #[0]VAR)
                            (#[0]NEG (#[0]↑APPLY ⌞ f ⌟ #[0]VAR)))


#MPℙ-right : CTerm → CTerm
#MPℙ-right f = #SQUASH (#SUM #NAT! (#[0]↑APPLY ⌞ f ⌟ #[0]VAR))


#MPℙ-left : CTerm → CTerm
#MPℙ-left f = #NEG (#NEG (#MPℙ-right f))


#MPℙ : ℕ → CTerm
#MPℙ i = #PI (#NAT!→U i) (#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right))


-- sanity check
⌜#MPℙ⌝ : (i : ℕ) → ⌜ #MPℙ i ⌝ ≡ MPℙ i
⌜#MPℙ⌝ i = refl


sub0-fun-mpℙ : (a : CTerm) → sub0 a (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)
                              ≡ #FUN (#MPℙ-left a) (#MPℙ-right a)
sub0-fun-mpℙ a =
  ≡sub0-#[0]FUN
    a #[0]MPℙ-left #[0]MPℙ-right (#MPℙ-left a) (#MPℙ-right a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡LIFT (≡APPLY e1 refl)))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT! (#[1]LIFT (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT! (#[0]LIFT (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡LIFT (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl

    e1 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 (CTerm.cTerm a))))
         ≡ shiftUp 1 (CTerm0.cTerm (CTerm→CTerm0 a))
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mpℙ2 : (a : CTerm)
              → sub0 a (#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right))
              ≡ #FUN (#DECℕ a) (#FUN (#MPℙ-left a) (#MPℙ-right a))
sub0-fun-mpℙ2 a =
  ≡sub0-#[0]FUN
    a #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)
    (#DECℕ a) (#FUN (#MPℙ-left a) (#MPℙ-right a))
    (CTerm≡ (≡PI refl (≡SET refl (≡UNION (≡LIFT (≡APPLY e1 refl)) (≡PI (≡LIFT (≡APPLY e1 refl)) refl)))))
    (sub0-fun-mpℙ a)
  where
    e1 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))
       ≡ shiftUp 0 (CTerm0.cTerm (CTerm→CTerm0 a))
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftDown 2 a = refl


sub0-#[0]↑APPLY : (a n : CTerm)
                → sub0 n (#[0]↑APPLY ⌞ a ⌟ #[0]VAR)
                ≡ #↑APPLY a n
sub0-#[0]↑APPLY a n = CTerm≡ (≡LIFT (≡APPLY e1 e2))
  where
    e1 : shiftDown 0 (subv 0 (shiftUp 0 ⌜ n ⌝) (CTerm0.cTerm (CTerm→CTerm0 a)))
       ≡ ⌜ a ⌝
    e1 rewrite #shiftUp 0 n | #subv 0 ⌜ n ⌝ ⌜ a ⌝ (CTerm.closed a) | #shiftDown 0 a = refl

    e2 : shiftDown 0 (shiftUp 0 ⌜ n ⌝)
       ≡ ⌜ n ⌝
    e2 rewrite #shiftUp 0 n | #shiftDown 0 n = refl


{-
sub0-LIFT-APPLY : (a b : CTerm) → sub0 a (#[0]LIFT (#[0]APPLY ⌞ b ⌟ #[0]VAR)) ≡ #LIFT (#APPLY b a)
sub0-LIFT-APPLY a b = CTerm≡ (≡LIFT (→≡APPLY x y))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl
-}


isType-MPℙ-right-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                      → equalInType (suc i) w (#NAT!→U i) f₁ f₂
                      → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType (suc i) w' #NAT! a b)
                                     → equalTypes (suc i) w' (sub0 a (#[0]↑APPLY ⌞ f₁ ⌟ #[0]VAR))
                                                             (sub0 b (#[0]↑APPLY ⌞ f₂ ⌟ #[0]VAR)))
isType-MPℙ-right-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-#[0]↑APPLY f₁ a₁))
    (sym (sub0-#[0]↑APPLY f₂ a₂))
    (equalTypes-LIFT2
      i w1 (#APPLY f₁ a₁) (#APPLY f₂ a₂)
      (equalInType→equalTypes-aux
        (suc i) i ≤-refl w1 (#APPLY f₁ a₁) (#APPLY f₂ a₂)
        (equalInType-FUN→ (≡CTerm→equalInType (#NAT!→U≡ i) f∈) w1 e1 a₁ a₂ a∈)))


→equalTypes-#MPℙ-right : {i : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                       → equalInType (suc i) w (#NAT!→U i) a₁ a₂
                       → equalTypes (suc i) w (#MPℙ-right a₁) (#MPℙ-right a₂)
→equalTypes-#MPℙ-right {i} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (eqTypesSUM← (λ w' _ → isTypeNAT!) (isType-MPℙ-right-body i w a₁ a₂ eqt))


→equalTypes-#MPℙ-left : {i : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                       → equalInType (suc i) w (#NAT!→U i) a₁ a₂
                       → equalTypes (suc i) w (#MPℙ-left a₁) (#MPℙ-left a₂)
→equalTypes-#MPℙ-left {i} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (→equalTypes-#MPℙ-right eqt))


{-
-- This is the axiom of unique choice
--     Π(R : ℕ→𝔹→ℙ).
--        (Π(n:ℕ).∃(b:𝔹).R n b)
--        → (Π(n:ℕ)(b₁:𝔹)(b₂:𝔹).R n b₁ → R n b₂ → b₁=b₂)
--        → ∃(f:ℕ→𝔹).Π(n:ℕ).R n (f n)
-- Could we prove that this is not valid using a choice δ and the relation
--     R n true  = ∀m≥n.δ(m)=0
--     R n false = ¬∀m≥n.δ(m)=0
-- ?
-- If that was the case, we would also be able to invalidate AC₀₀
-- If we want to use it for MP, we probably want #NAT! not #NAT
#uniqueChoice : ℕ → CTerm
#uniqueChoice i =
  #PI (#FUN #NAT (#FUN #BOOL (#UNIV i))) -- R
      (#[0]FUN
        (#[0]PI #[0]NAT (#[1]SQUASH (#[1]SUM #[1]BOOL (#[2]APPLY2 #[2]VAR2 #[2]VAR1 #[2]VAR0)))) -- Condition
        (#[0]FUN
          (#[0]PI #[0]NAT (#[1]PI #[1]BOOL (#[2]PI #[2]BOOL (#[3]FUN (#[3]APPLY2 #[3]VAR3 #[3]VAR2 #[3]VAR1)
                                                                     (#[3]FUN (#[3]APPLY2 #[3]VAR3 #[3]VAR2 #[3]VAR0)
                                                                              (#[3]EQ #[3]VAR1 #[3]VAR0 #[3]BOOL))))))
          (#[0]SQUASH (#[0]SUM (#[0]FUN #[0]NAT #[0]BOOL) (#[1]PI #[1]NAT (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0)))))))
-}


Choiceℙ : ℕ → ChoiceBar W M C K P G X N EC V F E → Set
Choiceℙ i cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #UNIV i
  × Cℂ₀ ≡ #FALSE
  × Cℂ₁ ≡ #TRUE


-- Same as in not_mp. Move it.
-- alwaysFreezable is only going to be true about choice sequences, but not about references, which change over time
alwaysFreezable : Freeze W C K P G N → Set(L)
alwaysFreezable f = (c : Name) (w : 𝕎·) → Freeze.freezable f c w


isType-#NAT!→U : (w : 𝕎·) (n : ℕ) → isType (suc n) w (#NAT!→U n)
isType-#NAT!→U w n
  rewrite #NAT!→U≡ n
  = eqTypesFUN← isTypeNAT! (eqTypesUniv w (suc n) n ≤-refl)


sub0-DECℕ-body1 : (a n : CTerm)
                → sub0 n (#[0]OR (#[0]↑APPLY ⌞ a ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ a ⌟ #[0]VAR)))
                ≡ #OR (#↑APPLY a n) (#NEG (#↑APPLY a n))
sub0-DECℕ-body1 a n = CTerm≡ (≡SET refl (≡UNION (≡LIFT (≡APPLY e1 e2)) (≡PI (≡LIFT (≡APPLY e1 e2)) refl)))
  where
    e1 : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ n ⌝)) (shiftUp 0 (CTerm0.cTerm (CTerm→CTerm0 a))))
       ≡ shiftUp 0 ⌜ a ⌝
    e1 rewrite #shiftUp 0 a | #shiftUp 0 n | #shiftUp 0 n
             | #subv 1 ⌜ n ⌝ ⌜ a ⌝ (CTerm.closed a) | #shiftDown 1 a = refl

    e2 : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ n ⌝))
       ≡ shiftUp 0 ⌜ n ⌝
    e2 rewrite #shiftUp 0 n | #shiftUp 0 n | #shiftDown 1 n = refl


eqTypesOR← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
           → equalTypes i w A B
           → equalTypes i w C D
           → equalTypes i w (#OR A C) (#OR B D)
eqTypesOR← {w} {i} {A} {B} {C} {D} eqt1 eqt2 =
  eqTypesSQUASH← (eqTypesUNION← eqt1 eqt2)


→equalInTypeORₗ : {w : 𝕎·} {i : ℕ} {A B a b : CTerm} (u : CTerm)
                → ∈Type i w A u
                → isType i w B
                → equalInType i w (#OR A B) a b
→equalInTypeORₗ {w} {i} {A} {B} {a} {b} u a∈ tyb =
  →equalInType-SQUASH (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' _ → inhType i w' (#UNION A B))
  aw w1 e1 =
    #INL u ,
    →equalInType-UNION
      (eqTypes-mon (uni i) (fst a∈) w1 e1)
      (eqTypes-mon (uni i) tyb w1 e1)
      (Mod.∀𝕎-□ M aw1)
    where
    aw1 : ∀𝕎 w1 (λ w' _ → UNIONeq (equalInType i w' A) (equalInType i w' B) w' (#INL u) (#INL u))
    aw1 w2 e2 = u , u , inj₁ (⇓-refl ⌜ #INL u ⌝ w2 , ⇓-refl ⌜ #INL u ⌝ w2 , equalInType-mon a∈ w2 (⊑-trans· e1 e2))


→equalInTypeORᵣ : {w : 𝕎·} {i : ℕ} {A B a b : CTerm} (u : CTerm)
                → isType i w A
                → ∈Type i w B u
                → equalInType i w (#OR A B) a b
→equalInTypeORᵣ {w} {i} {A} {B} {a} {b} u tya b∈ =
  →equalInType-SQUASH (Mod.∀𝕎-□ M aw)
  where
  aw : ∀𝕎 w (λ w' _ → inhType i w' (#UNION A B))
  aw w1 e1 =
    #INR u ,
    →equalInType-UNION
      (eqTypes-mon (uni i) tya w1 e1)
      (eqTypes-mon (uni i) (fst b∈) w1 e1)
      (Mod.∀𝕎-□ M aw1)
    where
    aw1 : ∀𝕎 w1 (λ w' _ → UNIONeq (equalInType i w' A) (equalInType i w' B) w' (#INR u) (#INR u))
    aw1 w2 e2 = u , u , inj₂ (⇓-refl ⌜ #INR u ⌝ w2 , ⇓-refl ⌜ #INR u ⌝ w2 , equalInType-mon b∈ w2 (⊑-trans· e1 e2))


→equalTypes-#DECℕ-bodyₗ : {i : ℕ} {w : 𝕎·} {a₁ a₂ n₁ n₂ : CTerm}
                        → equalInType (suc i) w (#NAT!→U i) a₁ a₂
                        → equalInType (suc i) w #NAT! n₁ n₂
                        → equalTypes (suc i) w (#↑APPLY a₁ n₁) (#↑APPLY a₂ n₂)
→equalTypes-#DECℕ-bodyₗ {i} {w} {a₁} {a₂} {n₁} {n₂} a∈ n∈ =
  equalTypes-LIFT2
    i w (#APPLY a₁ n₁) (#APPLY a₂ n₂)
    (equalInType→equalTypes-aux (suc i) i ≤-refl w (#APPLY a₁ n₁) (#APPLY a₂ n₂)
      (equalInType-FUN→ (≡CTerm→equalInType (#NAT!→U≡ i) a∈) w (⊑-refl· w) n₁ n₂ n∈))


→equalTypes-#DECℕ-bodyᵣ : {i : ℕ} {w : 𝕎·} {a₁ a₂ n₁ n₂ : CTerm}
                        → equalInType (suc i) w (#NAT!→U i) a₁ a₂
                        → equalInType (suc i) w #NAT! n₁ n₂
                        → equalTypes (suc i) w (#NEG (#↑APPLY a₁ n₁)) (#NEG (#↑APPLY a₂ n₂))
→equalTypes-#DECℕ-bodyᵣ {i} {w} {a₁} {a₂} {n₁} {n₂} a∈ n∈ =
  eqTypesNEG← (→equalTypes-#DECℕ-bodyₗ a∈ n∈)


→equalTypes-#DECℕ-body : {i : ℕ} {w : 𝕎·} {a₁ a₂ n₁ n₂ : CTerm}
                       → equalInType (suc i) w (#NAT!→U i) a₁ a₂
                       → equalInType (suc i) w #NAT! n₁ n₂
                       → equalTypes (suc i) w
                                    (sub0 n₁ (#[0]OR (#[0]↑APPLY ⌞ a₁ ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                    (sub0 n₂ (#[0]OR (#[0]↑APPLY ⌞ a₂ ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ a₂ ⌟ #[0]VAR))))
→equalTypes-#DECℕ-body {i} {w} {a₁} {a₂} {n₁} {n₂} a∈ n∈
  rewrite sub0-DECℕ-body1 a₁ n₁ | sub0-DECℕ-body1 a₂ n₂
  = eqTypesOR← (→equalTypes-#DECℕ-bodyₗ a∈ n∈) (→equalTypes-#DECℕ-bodyᵣ a∈ n∈)


→equalTypes-#DECℕ : {i : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                  → equalInType (suc i) w (#NAT!→U i) a₁ a₂
                  → equalTypes (suc i) w (#DECℕ a₁) (#DECℕ a₂)
→equalTypes-#DECℕ {i} {w} {a₁} {a₂} a∈ =
  eqTypesPI← (λ w1 e1 → isTypeNAT!) aw
  where
    aw : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) (ea : equalInType (suc i) w' #NAT! n₁ n₂)
                      → equalTypes (suc i) w'
                                   (sub0 n₁ (#[0]OR (#[0]↑APPLY ⌞ a₁ ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                   (sub0 n₂ (#[0]OR (#[0]↑APPLY ⌞ a₂ ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ a₂ ⌟ #[0]VAR)))))
    aw w1 e1 n₁ n₂ n∈ = →equalTypes-#DECℕ-body (equalInType-mon a∈ w1 e1) n∈


isTypeMPℙ : (w : 𝕎·) (n : ℕ) → isType (suc n) w (#MPℙ n)
isTypeMPℙ w n =
  eqTypesPI←
    {w} {suc n}
    {#NAT!→U n} {#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)}
    {#NAT!→U n} {#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)}
    (λ w1 e1 → isType-#NAT!→U w1 n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType (suc n) w' (#NAT!→U n) a₁ a₂
                      → equalTypes (suc n) w' (sub0 a₁ (#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)))
                                              (sub0 a₂ (#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right))))
    aw w1 e1 a₁ a₂ a∈ rewrite sub0-fun-mpℙ2 a₁ | sub0-fun-mpℙ2 a₂ = c
      where
        c : equalTypes (suc n) w1 (#FUN (#DECℕ a₁) (#FUN (#MPℙ-left a₁) (#MPℙ-right a₁)))
                                  (#FUN (#DECℕ a₂) (#FUN (#MPℙ-left a₂) (#MPℙ-right a₂)))
        c = eqTypesFUN← (→equalTypes-#DECℕ a∈) (eqTypesFUN← (→equalTypes-#MPℙ-left a∈) (→equalTypes-#MPℙ-right a∈))


equalInType-#MPℙ-right→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                        → ∈Type (suc i) w (#NAT!→U i) f
                        → equalInType (suc i) w (#MPℙ-right f) a₁ a₂
                        → □· w (λ w' _ → Σ CTerm (λ n → ∈Type i w' #NAT! n
                                         × inhType i w' (#APPLY f n)))
equalInType-#MPℙ-right→ i w f a₁ a₂ f∈ h =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-SQUASH→ h))
    where
    aw : ∀𝕎 w (λ w' e' → inhType (suc i) w' (#SUM #NAT! (#[0]↑APPLY ⌞ f ⌟ #[0]VAR))
                       → □· w' (↑wPred' (λ w'' _ → Σ CTerm (λ n → ∈Type i w'' #NAT! n × inhType i w'' (#APPLY f n))) e'))
    aw w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw1 (equalInType-SUM→ t∈)
      where
      aw1 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType (suc i) w' #NAT!) (λ a b ea → equalInType (suc i) w' (sub0 a (#[0]↑APPLY ⌞ f ⌟ #[0]VAR))) w' t t
                           → ↑wPred' (λ w'' _ → Σ CTerm (λ n → ∈Type i w'' #NAT! n × inhType i w'' (#APPLY f n))) e1 w' e')
      aw1 w1 e2 (a1 , a2 , b1 , b2 , a∈ , c1 , c2 , b∈) z
        rewrite sub0-#[0]↑APPLY f a1
        = a1 , ∈NAT!-change-level (suc i) i (equalInType-refl a∈) ,
          b1 , equalInType-refl (equalInType-LIFT→ i w1 (#APPLY f a1) b1 b2 b∈)


-- Application to 2 arguments
#APPLY2 : CTerm → CTerm → CTerm → CTerm
#APPLY2 f a b = #APPLY (#APPLY f a) b


-- Application to 3 arguments
#APPLY3 : CTerm → CTerm → CTerm → CTerm → CTerm
#APPLY3 f a b c = #APPLY (#APPLY (#APPLY f a) b) c


#AX∈DECℕ : {i : ℕ} {w : 𝕎·} {f : CTerm}
         → inhType i w (#DECℕ f)
         → equalInType i w (#DECℕ f) #AX #AX
#AX∈DECℕ {i} {w} {f} (t , t∈) =
  equalInType-PI
    (λ w1 e1 → eqTypes-mon (uni i) (fst (equalInType-PI→ t∈)) w1 e1)
    (fst (snd (equalInType-PI→ t∈)))
    λ w1 e1 a₁ a₂ a∈ →
      ≡CTerm→equalInType
        (sym (sub0-DECℕ-body1 f a₁))
        (→equalInType-SQUASH
          (equalInType-SQUASH→
            {i} {w1} {_} {#APPLY t a₁} {#APPLY t a₂}
            (≡CTerm→equalInType (sub0-DECℕ-body1 f a₁) (snd (snd (equalInType-PI→ t∈)) w1 e1 a₁ a₂ a∈))))


→equalInType-#MPℙ-left : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                       → ∈Type (suc i) w (#NAT!→U i) f
                       → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n × inhType i w' (#APPLY f n)))
                                                      → ⊥)
                                      → ⊥)
                       → equalInType (suc i) w (#MPℙ-left f) a₁ a₂
→equalInType-#MPℙ-left i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (→equalTypes-#MPℙ-right f∈))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType (suc i) w' (#NEG (#MPℙ-right f)) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n × inhType i w' (#APPLY f n))) → ⊥)
        aw2 w2 e2 (n , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType (suc i) w' (#SUM #NAT! (#[0]↑APPLY ⌞ f ⌟ #[0]VAR)))
            i∈ w3 e3 =
              #PAIR n t ,
              equalInType-SUM
                (λ w' _ → isTypeNAT!)
                (isType-MPℙ-right-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT!)
                                            (λ a b ea → equalInType (suc i) w' (sub0 a (#[0]↑APPLY ⌞ f ⌟ #[0]VAR)))
                                            w' (#PAIR n t) (#PAIR n t))
                aw3 w4 e4 =
                  n , n , t , t ,
                  equalInType-refl (equalInType-mon (∈NAT!-change-level i (suc i) n∈) w4 (⊑-trans· e3 e4)) ,
                  ⇓-refl ⌜ #PAIR n t ⌝ w4 ,
                  ⇓-refl ⌜ #PAIR n t ⌝ w4 ,
                  ≡CTerm→equalInType
                    (sym (sub0-#[0]↑APPLY f n))
                    (equalInType-LIFT← i w4 (#APPLY f n) t t (equalInType-mon inh w4 (⊑-trans· e3 e4)))

            s∈ : equalInType (suc i) w2 (#MPℙ-right f) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)


∈#MPℙ→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
       → equalInType (suc i) w (#MPℙ i) F G
       → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type (suc i) w' (#NAT!→U i) f
                      → inhType (suc i) w' (#DECℕ f)
                      → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n
                                                         × inhType i w' (#APPLY f n)))
                                                      → ⊥)
                                      → ⊥)
                      → □· w' (λ w' _ → Σ CTerm (λ n → ∈Type i w' #NAT! n
                                        × inhType i w' (#APPLY f n))))
∈#MPℙ→ i w F G F∈ w1 e1 f f∈ decn cond =
  equalInType-#MPℙ-right→ i w1 f (#APPLY3 F f #AX #AX) (#APPLY3 G f #AX #AX) f∈ h4
  where
    h1 : equalInType (suc i) w1 (sub0 f (#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right))) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {suc i} {w} {#NAT!→U i} {#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)} F∈)) w1 e1 f f f∈

    h2 : equalInType (suc i) w1 (#FUN (#DECℕ f) (#FUN (#MPℙ-left f) (#MPℙ-right f))) (#APPLY F f) (#APPLY G f)
    h2 = ≡CTerm→equalInType (sub0-fun-mpℙ2 f) h1

    h3 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType (suc i) w' (#DECℕ f) a₁ a₂
                       → (b₁ b₂ : CTerm) → equalInType (suc i) w' (#MPℙ-left f) b₁ b₂
                       → equalInType (suc i) w' (#MPℙ-right f) (#APPLY3 F f a₁ b₁) (#APPLY3 G f a₂ b₂))
    h3 w2 e2 a₁ a₂ a∈ b₁ b₂ b∈ =
      equalInType-FUN→
        {suc i} {w2} {#MPℙ-left f} {#MPℙ-right f} {#APPLY2 F f a₁} {#APPLY2 G f a₂}
        (equalInType-FUN→ h2 w2 e2 a₁ a₂ a∈)
        w2 (⊑-refl· w2) b₁ b₂ b∈

    h4 : equalInType (suc i) w1 (#MPℙ-right f) (#APPLY3 F f #AX #AX) (#APPLY3 G f #AX #AX)
    h4 = h3 w1 (⊑-refl· w1) #AX #AX (#AX∈DECℕ decn) #AX #AX (→equalInType-#MPℙ-left i w1 f #AX #AX f∈ cond)


-- MOVE to props1
eqTypes-UNIV→< : (i n : ℕ) (w : 𝕎·) (A B : CTerm)
               → A #⇛ #UNIV i at w
               → equalTypes n w A B
               → i < n
eqTypes-UNIV→< i n w A B comp eqt = concl i comp
  where
  ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2)
      → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2')
         → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → (i : ℕ) → T1' #⇛ #UNIV i at w' → i < u')
      → (i : ℕ) → T1 #⇛ #UNIV i at w → i < u
  ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind i comp = ⊥-elim (UNIVneqQNAT (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind i comp = ⊥-elim (UNIVneqLT (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind i comp = ⊥-elim (UNIVneqQLT (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind i comp = ⊥-elim (UNIVneqFREE (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind i comp = ⊥-elim (UNIVneqPI (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind i comp = ⊥-elim (UNIVneqW (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind i comp = ⊥-elim (UNIVneqM (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind i comp = ⊥-elim (UNIVneqSUM (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind i comp = ⊥-elim (UNIVneqSET (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind i comp = ⊥-elim (UNIVneqISECT (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind i comp = ⊥-elim (UNIVneqTUNION (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) ind i comp = ⊥-elim (UNIVneqEQ (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind i comp = ⊥-elim (UNIVneqUNION (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind i comp = ⊥-elim (UNIVneqNOWRITE (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind i comp = ⊥-elim (UNIVneqNOREAD (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind i comp = ⊥-elim (UNIVneqSUBSING (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind i comp = ⊥-elim (UNIVneqFFDEFS (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind i comp = ⊥-elim (UNIVneqPURE (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind i comp = ⊥-elim (UNIVneqNOSEQ (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) ind i comp = ⊥-elim (UNIVneqTERM (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) ind i comp = c
    where
    c : i < u
    c rewrite UNIVinj (⇛-val-det tt tt comp x) = p
  ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) ind i comp = ⊥-elim (UNIVneqLIFT (⇛-val-det tt tt comp x))
  ind {u} {w} {T1} {T2} (EQTBAR x) ind i comp =
    lower {0ℓ} {lsuc(L)} (Mod.□-const M (∀𝕎-□at W M x aw))
      where
      aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2) → at□· x w' e' z → Lift (lsuc L) (i < u))
      aw w1 e1 z at = lift (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w1 e1 z at)) i (⇛-mon e1 comp))

  concl : (i : ℕ) → A #⇛ #UNIV i at w → i < n
  concl i comp =
    equalTypes-ind
      (λ {n} {w} {A} {B} eqt → (i : ℕ) → A #⇛ #UNIV i at w → i < n)
      ind eqt i comp


-- MOVE to props3
equalTerms-pres-#⇛-left-rev-UNIV : (i : ℕ) → equalTerms-pres-#⇛-left-rev (#UNIV i)
equalTerms-pres-#⇛-left-rev-UNIV i {j} {w} {a} {b} {c} comp eqt eqi =
  equalInType→eqInType
    {j} {w} {#UNIV i} {#UNIV i} {#UNIV i} {a} {c} refl {eqt}
    (equalTypes→equalInType-UNIV
      {j} {i} (eqTypes-UNIV→< i j w (#UNIV i) (#UNIV i) (#⇛-refl w (#UNIV i)) eqt) {w} {a} {c}
      (equalTypes-#⇛-left-right-rev
        {i} {w} {b} {a} {c} {c} (#⇛!→#⇛ {w} {a} {b} comp) (#⇛-refl w c)
        (equalInType→equalTypes-aux
          j i (eqTypes-UNIV→< i j w (#UNIV i) (#UNIV i) (#⇛-refl w (#UNIV i)) eqt) w b c
          (eqInType→equalInType {j} {w} {#UNIV i} {#UNIV i} {#UNIV i} {b} {c} refl eqt eqi))))


abstract
  equalInType-EQ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                 → equalInType u w (#EQ a b A) f g
                 → equalInType u w A a b
  equalInType-EQ {u} {w} {a} {b} {A} {f} {g} f∈ =
    equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 h → h) (equalInType-EQ→ f∈))


¬ΣNAT!→¬inhType-Σchoiceℙ : (i : ℕ) → Choiceℙ i CB → (w : 𝕎·) (name : Name)
                         → ∀𝕎 w (λ w' _ → ¬ Σ CTerm (λ n → ∈Type i w' #NAT! n × inhType i w' (#APPLY (#CS name) n)))
                         → ∀𝕎 w (λ w' _ → ¬ inhType (suc i) w' (#Σchoice name ℂ₁·))
¬ΣNAT!→¬inhType-Σchoiceℙ i cp w name aw w1 e1 (t , inh) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
  where
    h0 : ∈Type (suc i) w1 (#SUM #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) t
    h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) inh

    h1 : □· w1 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT!) (λ a b ea → equalInType (suc i) w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' t t)
    h1 = equalInType-SUM→ h0

    aw3 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType (suc i) w' #NAT!)
                                 (λ a b ea → equalInType (suc i) w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                 w' t t
                         → Lift (lsuc L) ⊥)
    aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (aw w2 (⊑-trans· e1 e2) (a₁ , ∈NAT!-change-level (suc i) i (equalInType-refl ea) , b₁ , equalInType-refl eqi2))
          where
            eqi1 : equalInType (suc i) w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi3 : equalInType (suc i) w2 (#EQ (#APPLY (#CS name) a₁) #TRUE (#UNIV i)) b₁ b₂
            eqi3 = ≡CTerm→equalInType (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd cp)) (fst cp)) eqi1

            eqi4 : equalInType (suc i) w2 (#UNIV i) (#APPLY (#CS name) a₁) #TRUE
            eqi4 = equalInType-EQ eqi3

            eqi5 : equalTypes i w2 (#APPLY (#CS name) a₁) #TRUE
            eqi5 = equalInType→equalTypes-aux (suc i) i ≤-refl w2 (#APPLY (#CS name) a₁) #TRUE eqi4

            eqi2 : equalInType i w2 (#APPLY (#CS name) a₁) b₁ b₂
            eqi2 = TSext-equalTypes-equalInType i w2 #TRUE (#APPLY (#CS name) a₁) b₁ b₂ (TEQsym-equalTypes i w2 _ _ eqi5) (→equalInType-TRUE i)


-- This assumption is only true about choice sequences and not about refences
-- It says that choices never change
immutableChoices : Set(lsuc(L))
immutableChoices =
    (w : 𝕎·) (name : Name) (n : ℕ) (c : ℂ·)
  → getChoice· n name w ≡ just c
  → ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (getChoice· n name w' ≡ just c))


immutableChoices→ : immutableChoices
                  → (w : 𝕎·) (name : Name) (n : ℕ) (r : Res)
                  → compatible· name w r
                  → □· w (λ w' _ → Σ ℂ· (λ c → ·ᵣ r n c × ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (getChoice· n name w'' ≡ just c))))
immutableChoices→ imut w name n r compat =
  Mod.∀𝕎-□Func M aw (□·-choice· w name n r compat)
    where
    aw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (λ w'' _ → Lift (lsuc L) (Σ ℂ· (λ t → getChoice· n name w'' ≡ just t × ·ᵣ r n t)))
                       → Σ ℂ· (λ c → ·ᵣ r n c × ∀𝕎 w' (λ w'' _ → Lift (lsuc L) (getChoice· n name w'' ≡ just c))))
    aw w1 e1 h = fst q , snd (snd q) , imut w1 name n (proj₁ q) (fst (snd q))
      where
      q : Σ ℂ· (λ t → getChoice· n name w1 ≡ just t × ·ᵣ r n t)
      q = lower (h w1 (⊑-refl· w1))


-- A stronger version than the one in barContP7
equalInType-#⇛-rev : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                      → U #⇛ T at w
                      → equalInType i w T a b
                      → equalInType i w U a b
equalInType-#⇛-rev {i} {w} {T} {U} {a} {b} comp e =
  TSext-equalTypes-equalInType
    i w T U a b
    (equalTypes-#⇛-left-right-rev {i} {w} {T} {T} {U} {T} (#⇛-refl w T) comp (fst e))
    e

#⇛-vals-det→ : {w : 𝕎·} {a b c : CTerm}
             → #isValue b
             → #isValue c
             → a #⇛ b at w
             → a #⇛ c at w
             → b #⇛ c at w
#⇛-vals-det→ {w} {a} {b} {c} isvb isvc compb compc
  rewrite #⇛-val-det {w} {a} {b} {c} isvb isvc compb compc
  = #⇛-refl w c


abstract
  equalTypes-#⇛-left-val : {i : ℕ} {w : 𝕎·} {a b c : CTerm}
                         → a #⇛ b at w
                         → #isValue b
                         → equalTypes i w a c
                         → equalTypes i w b c
  equalTypes-#⇛-left-val {i} {w} {a} {b} {c} comp isv eqt = concl b comp isv
    where
      ind : {u : ℕ} {w : 𝕎·} {a c : CTerm} (eqt : equalTypes u w a c)
            → ({u' : ℕ} {w' : 𝕎·} {a' c' : CTerm} (eqt' : equalTypes u' w' a' c') → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt
                → (b' : CTerm) → a' #⇛ b' at w' → #isValue b' → equalTypes u' w' b' c')
            → (b : CTerm) → a #⇛ b at w → #isValue b → equalTypes u w b c
      ind {u} {w} {a} {c} (EQTQNAT x x₁) ind b comp isv =
        EQTQNAT (#⇛-vals-det→ {_} {a} {b} {#QNAT} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind b comp isv =
        EQTLT a1 a2 b1 b2 (#⇛-vals-det→ {_} {a} {b} {#LT a1 b1} isv tt comp x) x₁ x₂ x₃
      ind {u} {w} {a} {c} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind b comp isv =
        EQTQLT a1 a2 b1 b2 (#⇛-vals-det→ {_} {a} {b} {#QLT a1 b1} isv tt comp x) x₁ x₂ x₃
      ind {u} {w} {a} {c} (EQTFREE x x₁) ind b comp isv =
        EQTFREE (#⇛-vals-det→ {_} {a} {b} {#FREE} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind b comp isv =
        EQTPI A1 B1 A2 B2 (#⇛-vals-det→ {_} {a} {b} {#PI A1 B1} isv tt comp x) x₁ eqta eqtb exta extb
      ind {u} {w} {a} {c} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind b comp isv =
        EQTSUM A1 B1 A2 B2 (#⇛-vals-det→ {_} {a} {b} {#SUM A1 B1} isv tt comp x) x₁ eqta eqtb exta extb
      ind {u} {w} {a} {c} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind b comp isv =
        EQTW A1 B1 C1 A2 B2 C2 (#⇛-vals-det→ {_} {a} {b} {#WT A1 B1 C1} isv tt comp x) x₁ eqta eqtb eqtc exta extb extc
      ind {u} {w} {a} {c} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) ind b comp isv =
        EQTM A1 B1 C1 A2 B2 C2 (#⇛-vals-det→ {_} {a} {b} {#MT A1 B1 C1} isv tt comp x) x₁ eqta eqtb eqtc exta extb extc
      ind {u} {w} {a} {c} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind b comp isv =
        EQTSET A1 B1 A2 B2 (#⇛-vals-det→ {_} {a} {b} {#SET A1 B1} isv tt comp x) x₁ eqta eqtb exta extb
      ind {u} {w} {a} {c} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind b comp isv =
        EQTISECT A1 B1 A2 B2 (#⇛-vals-det→ {_} {a} {b} {#ISECT A1 B1} isv tt comp x) x₁ eqtA eqtB exta extb
      ind {u} {w} {a} {c} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ind b comp isv =
        EQTTUNION A1 B1 A2 B2 (#⇛-vals-det→ {_} {a} {b} {#TUNION A1 B1} isv tt comp x) x₁ eqta eqtb exta extb
      ind {u} {w} {a} {c} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) ind b comp isv =
        EQTEQ a1 b1 a2 b2 A B (#⇛-vals-det→ {_} {a} {b} {#EQ a1 a2 A} isv tt comp x) x₁ eqtA exta eqt1 eqt2
      ind {u} {w} {a} {c} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ind b comp isv =
        EQTUNION A1 B1 A2 B2 (#⇛-vals-det→ {_} {a} {b} {#UNION A1 B1} isv tt comp x) x₁ eqtA eqtB exta extb
      ind {u} {w} {a} {c} (EQTNOWRITE x x₁) ind b comp isv =
        EQTNOWRITE (#⇛-vals-det→ {_} {a} {b} {#NOWRITE} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTNOREAD x x₁) ind b comp isv =
        EQTNOREAD (#⇛-vals-det→ {_} {a} {b} {#NOREAD} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTSUBSING A1 A2 x x₁ eqtA exta) ind b comp isv =
        EQTSUBSING A1 A2 (#⇛-vals-det→ {_} {a} {b} {#SUBSING A1} isv tt comp x) x₁ eqtA exta
      ind {u} {w} {a} {c} (EQTPURE x x₁) ind b comp isv =
        EQTPURE (#⇛-vals-det→ {_} {a} {b} {#PURE} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTNOSEQ x x₁) ind b comp isv =
        EQTNOSEQ (#⇛-vals-det→ {_} {a} {b} {#NOSEQ} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTTERM t1 t2 x x₁ x₂) ind b comp isv =
        EQTTERM t1 t2 (#⇛-vals-det→ {_} {a} {b} {#TERM t1} isv tt comp x) x₁ x₂
      ind {u} {w} {a} {c} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ind b comp isv =
        EQFFDEFS A1 A2 x1 x2 (#⇛-vals-det→ {_} {a} {b} {#FFDEFS A1 x1} isv tt comp x) x₁ eqtA exta eqx
      ind {u} {w} {a} {c} (EQTUNIV i₁ p x x₁) ind b comp isv =
        EQTUNIV i₁ p (#⇛-vals-det→ {_} {a} {b} {#UNIV i₁} isv tt comp x) x₁
      ind {u} {w} {a} {c} (EQTLIFT A1 A2 x x₁ eqtA exta) ind b comp isv =
        EQTLIFT A1 A2 (#⇛-vals-det→ {_} {a} {b} {#LIFT A1} isv tt comp x) x₁ eqtA exta
      ind {u} {w} {a} {c} (EQTBAR x) ind b comp isv =
        EQTBAR (∀𝕎-□at W M x (λ w' e' z at → ind {u} {w'} {a} {c} z (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w a c x w' e' z at)) b (∀𝕎-mon e' comp) isv))

      concl : (b : CTerm) → a #⇛ b at w → #isValue b → equalTypes i w b c
      concl b comp isv =
        equalTypes-ind
          (λ {i} {w} {a} {c} eqt → (b : CTerm) → a #⇛ b at w → #isValue b → equalTypes i w b c)
          ind eqt b comp isv


equalTypes-#⇛-left-right-val : {i : ℕ} {w : 𝕎·} {a b c d : CTerm}
                             → a #⇛ b at w
                             → d #⇛ c at w
                             → #isValue b
                             → #isValue c
                             → equalTypes i w a d
                             → equalTypes i w b c
equalTypes-#⇛-left-right-val {i} {w} {a} {b} {c} {d} c₁ c₂ isvb isvc eqt =
  equalTypes-#⇛-left-val c₁ isvb (TEQsym-equalTypes i w _ _ (equalTypes-#⇛-left-val c₂ isvc (TEQsym-equalTypes i w _ _ eqt)))


equalInType-#⇛-val : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                   → T #⇛ U at w
                   → #isValue U
                   → equalInType i w T a b
                   → equalInType i w U a b
equalInType-#⇛-val {i} {w} {T} {U} {a} {b} comp isv e =
  TSext-equalTypes-equalInType
    i w T U a b
    (TEQsym-equalTypes i w _ _ (equalTypes-#⇛-left-val comp isv (fst e)))
    e


getC-True→∈APPLY : (i : ℕ) (w : 𝕎·) (k : ℕ) (name : Name) (n : CTerm)
                 → ∀𝕎 w (λ w' e' → Lift (lsuc L) (getC k name w' ≡ just #TRUE))
                 → n #⇛! #NUM k at w
                 → equalInType i w (#APPLY (#CS name) n) #AX #AX
getC-True→∈APPLY i w k name n aw comp =
  equalInType-#⇛-rev
    {i} {w} {#TRUE} {#APPLY (#CS name) n} {#AX} {#AX}
    (⇛-trans (#⇛-APPLY-CS {_} {n} {#NUM k} name (#⇛!→#⇛ {_} {n} {#NUM k} comp)) comp')
    (→equalInType-TRUE i)
  where
  comp' : #APPLY (#CS name) (#NUM k) #⇛ #TRUE at w
  comp' w1 e1 = lift (1 , c)
    where
    c : stepsT 1 (APPLY (CS name) (NUM k)) w1 ≡ TRUE
    c rewrite lower (aw w1 e1) = refl


getC-False→∈APPLY : (i : ℕ) (w : 𝕎·) (k : ℕ) (name : Name) (n a b : CTerm)
                  → ∀𝕎 w (λ w' e' → Lift (lsuc L) (getC k name w' ≡ just #FALSE))
                  → n #⇛! #NUM k at w
                  → equalInType i w (#APPLY (#CS name) n) a b
                  → ⊥
getC-False→∈APPLY i w k name n a b aw comp a∈ =
  ¬equalInType-FALSE a∈'
  where
  comp' : #APPLY (#CS name) (#NUM k) #⇛ #FALSE at w
  comp' w1 e1 = lift (1 , c)
    where
    c : stepsT 1 (APPLY (CS name) (NUM k)) w1 ≡ FALSE
    c rewrite lower (aw w1 e1) = refl

  a∈' : equalInType i w #FALSE a b
  a∈' = equalInType-#⇛-val
          {i} {w} {#APPLY (#CS name) n} {#FALSE} {a} {b}
          (⇛-trans (#⇛-APPLY-CS {_} {n} {#NUM k} name (#⇛!→#⇛ {_} {n} {#NUM k} comp)) comp')
          tt a∈


inhType-DECℕ : (immut : immutableChoices) (i : ℕ) (cp : Choiceℙ i CB) (w : 𝕎·) (name : Name)
             → compatible· name w Resℂ
             → ∈Type (suc i) w (#NAT!→U i) (#CS name)
             → inhType (suc i) w (#DECℕ (#CS name))
inhType-DECℕ immut i cp w name compat f∈ =
  #lamAX ,
  equalInType-PI
    {_} {_} {#NAT!} {#[0]OR (#[0]↑APPLY ⌞ f ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ f ⌟ #[0]VAR))}
    (λ w' _ → isTypeNAT!)
    (λ w1 e1 n₁ n₂ n∈ → →equalTypes-#DECℕ-body (equalInType-mon f∈ w1 e1) n∈)
    aw
    where
    f : CTerm
    f = #CS name

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType (suc i) w' #NAT! a₁ a₂
                      → equalInType (suc i) w' (sub0 a₁ (#[0]OR (#[0]↑APPLY ⌞ f ⌟ #[0]VAR) (#[0]NEG (#[0]↑APPLY ⌞ f ⌟ #[0]VAR))))
                                    (#APPLY #lamAX a₁) (#APPLY #lamAX a₂))
    aw w1 e1 n₁ n₂ n∈ rewrite sub0-DECℕ-body1 f n₁ = c
      where
      c : equalInType (suc i) w1 (#OR (#↑APPLY f n₁) (#NEG (#↑APPLY f n₁))) (#APPLY #lamAX n₁) (#APPLY #lamAX n₂)
      c = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ (suc i) w1 n₁ n₂ n∈))
        where
        aw1 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                             → equalInType (suc i) w' (#OR (#↑APPLY f n₁) (#NEG (#↑APPLY f n₁))) (#APPLY #lamAX n₁) (#APPLY #lamAX n₂))
        aw1 w2 e2 (n , c₁ , c₂) =
          equalInType-local (Mod.∀𝕎-□Func M aw2 (immutableChoices→ immut w2 name n Resℂ (⊑-compatible· (⊑-trans· e1 e2) compat)))
          where
          aw2 : ∀𝕎 w2 (λ w' e' → Σ ℂ· (λ t → ·ᵣ Resℂ n t × ∀𝕎 w' (λ w'' _ → Lift (lsuc L) (getChoice· n name w'' ≡ just t)))
                               → equalInType (suc i) w' (#OR (#↑APPLY f n₁) (#NEG (#↑APPLY f n₁))) (#APPLY #lamAX n₁) (#APPLY #lamAX n₂))
          aw2 w3 e3 (c , sat , h) with sat
          ... | inj₁ z rewrite z = -- False case
            →equalInTypeORᵣ
              #AX
              (→equalTypes-#DECℕ-bodyₗ (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3)))
              (equalInType-NEG
                (→equalTypes-#DECℕ-bodyₗ (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3)))
                aw3)
            where
            h' : ∀𝕎 w3 (λ w' e' → Lift (lsuc L) (getC n name w' ≡ just #FALSE))
            h' w4 e4 rewrite lower (h w4 e4) | fst (snd cp) = lift refl

            aw3 : ∀𝕎 w3 (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType (suc i) w' (#↑APPLY f n₁) a₁ a₂)
            aw3 w4 e4 a₁ a₂ a∈ = getC-False→∈APPLY i w4 n name n₁ a₁ a₂ (∀𝕎-mon e4 h') (∀𝕎-mon (⊑-trans· e3 e4) c₁) (equalInType-LIFT→ i w4 (#APPLY f n₁) a₁ a₂ a∈)
          ... | inj₂ z rewrite z = -- True case
            →equalInTypeORₗ
              #AX
              (equalInType-LIFT← i w3 (#APPLY f n₁) #AX #AX (getC-True→∈APPLY i w3 n name n₁ h' (∀𝕎-mon e3 c₁)))
              (→equalTypes-#DECℕ-bodyᵣ (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3)))
            where
            h' : ∀𝕎 w3 (λ w' e' → Lift (lsuc L) (getC n name w' ≡ just #TRUE))
            h' w4 e4 rewrite lower (h w4 e4) | snd (snd cp) = lift refl


-- follows ¬MP₆ in not_mp
¬MPℙ : (i : ℕ) → Choiceℙ i CB → immutableChoices → alwaysFreezable F
     → (w : 𝕎·) → ∈Type (suc i) w (#NEG (#MPℙ i)) #lamAX
¬MPℙ i cp immut af w = equalInType-NEG (isTypeMPℙ w i) aw1
  where
  aw1 : ∀𝕎 w (λ w' _ →  (a₁ a₂ : CTerm) → ¬ equalInType (suc i) w' (#MPℙ i) a₁ a₂)
  aw1 w1 e1 F G F∈ = {!!}
    where
    aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type (suc i) w' (#NAT!→U i) f
                        → inhType (suc i) w' (#DECℕ f)
                        → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n
                                                           × inhType i w' (#APPLY f n)))
                                                        → ⊥)
                                        → ⊥)
                        → □· w' (λ w' _ → Σ CTerm (λ n → ∈Type i w' #NAT! n
                                          × inhType i w' (#APPLY f n))))
    aw2 = ∈#MPℙ→ i w1 F G F∈

    name : Name
    name = newChoice· w1

    w2 : 𝕎·
    w2 = startNewChoice Resℂ w1

    e2 : w1 ⊑· w2
    e2 = startNewChoice⊏ Resℂ w1

    oc1 : onlyℂ∈𝕎 (Res.def Resℂ) name w2
    oc1 n = getChoice-startNewChoice n Resℂ w1

    comp1 : compatible· name w2 Resℂ
    comp1 = startNewChoiceCompatible Resℂ w1

    fb1 : freezable· name w2
    fb1 = freezableStart· Resℂ w1

    f : CTerm
    f = #CS name

    eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType (suc i) w' (#UNIV i) (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
    eqf2 w' e m = ≡CTerm→equalInType (proj₁ cp) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! (suc i) w' m))

    eqf1 : ∈Type (suc i) w2 (#NAT!→U i) f
    eqf1 = ≡CTerm→equalInType
             (sym (#NAT!→U≡ i))
             (→equalInType-CS-NAT!→T (eqTypesUniv w2 (suc i) i ≤-refl) (equalTerms-pres-#⇛-left-rev-UNIV i) eqf2)

    h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n
                                          × inhType i w' (#APPLY f n)))
                                       → ⊥)
                       → ⊥)
    h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice (suc i) w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (af name w3) z
      where
      z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType (suc i) w4 (#Σchoice name ℂ₁·))
      z = ¬ΣNAT!→¬inhType-Σchoiceℙ i cp w3 name aw

    h4 : □· w2 (λ w' _ → Σ CTerm (λ n → ∈Type i w' #NAT! n × inhType i w' (#APPLY f n)))
    h4 = aw2 w2 e2 f eqf1 (inhType-DECℕ immut i cp w2 name comp1 eqf1) h3

\end{code}
