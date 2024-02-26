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
open import Axiom.ExcludedMiddle


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


module not_lpo {L  : Level}
               (W  : PossibleWorlds {L})
               (M  : Mod W)
               (C  : Choice)
               (K  : Compatible W C)
               (P  : Progress {L} W C K)
               (G  : GetChoice {L} W C K)
               (X  : ChoiceExt {L} W C)
               (N  : NewChoice {L} W C K G)
               (EC : Encode)
               (V  : ChoiceVal W C K G X N EC)
               (F  : Freeze {L} W C K P G N)
               (EM : ExcludedMiddle (lsuc(L)))
               (CB : ChoiceBar W M C K P G X N EC V F)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(EC)(V)
  using (¬∼ℂ₀₁· ; isValueℂ₀· ; isValueℂ₁·)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
  using (freezable· ; freezableStart·)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypes-mon ; ∀𝕎-□Func2)
--open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

--open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
--  using ()
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypesSQUASH← ; eqTypesUNION← ; eqTypesPI← ; eqTypesNEG← ; equalInType-PI→ ; ≡CTerm→equalInType ;
         NUM-equalInType-NAT! ; equalInType-NEG ; equalInType-refl ; equalInType-mon ; equalInType-SQUASH→ ;
         equalInType-NEG→ ; equalInType-PI ; →≡equalTypes ; →≡equalInType ; equalInType-local ; equalInType-sym ;
         isTypeNAT! ; equalInType-FUN→ ; equalInType-NAT!→)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (isType-#NAT!→BOOL₀ ; →equalInType-CS-NAT!→BOOL₀ ; fun-equalInType-SQUASH-UNION ; isType-#NAT!→BOOL₀! ;
         →equalInType-SQUASH ; →equalInType-CS-NAT!→BOOL₀! ; equalTypes→equalInType ; equalInType-#⇛-LR ;
         equalInType-BOOL₀!→ ; →equalInType-BOOL₀! ; equalInType-EQ→₁)
open import props4(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→equalInType-NAT!)
open import lem_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#SUM-ASSERT₂ ; #PI-NEG-ASSERT₂ ; →equalTypes-#SUM-ASSERT₂ ; →equalTypes-#PI-NEG-ASSERT₂ ; ASSERT₄ ;
         #[1]ASSERT₄ ; #SUM-ASSERT₄ ; #SUM-ASSERT₅ ; #PI-NEG-ASSERT₄ ; ≡ASSERT₄ ; →equalTypes-#SUM-ASSERT₅ ;
         →equalTypes-#PI-NEG-ASSERT₄ ; #[0]ASSERT₄ ; #ASSERT₄ ; sub0-NEG-ASSERT₄-APPLY ; #ASSERT₄≡ ;
         equalInType-BOOL₀!→equalTypes-ASSERT₄ ; sub0-ASSERT₄-APPLY)

open import props6(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypesUNION!← ; UNIONeq! ; equalInType-UNION! ; equalInType-UNION!→ ; SUMeq! ; equalInType-SUM!→ ;
         equalInType-#⇛ₚ-left-right-rev ; equalInType-SUM! ; →equalInType-EQ)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (followChoice· ; #[0]Typeℂ₀₁ ; Typeℂ₀₁·)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (sq-dec ; #Σchoice ; ¬-dec-Σchoice ; equalInType-#Σchoice ; ¬equalInType-#Σchoice ; ¬∀𝕎¬equalInType-#Σchoice ;
         sub0-#Σchoice-body≡ ; #Σchoice≡)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (Resℂ ; →equalInType-APPLY-CS-Typeℂ₀₁·)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (Bool₀ℂ ; Bool₀!ℂ ; #SUM-ASSERT₂→#Σchoice ; #PI-NEG-ASSERT₂→#Σchoice ; #SUM-ASSERT₅→#Σchoice)

open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (SUM! ; #SUM! ; UNION! ; #UNION!)

open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (≡SUM! ; #[0]SUM! ; ≡UNION! ; #[0]UNION!)

open import mp_props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (isType-#TPURE-NAT!→BOOL₀! ; equalInType-TPURE-NAT!→BOOL₀!ₗ ; equalInType-TPURE-NAT!→BOOL₀!ᵣ ;
         →equalInType-ASSERT₄ ; equalInType-ASSERT₄→ ; strongBool!-BTRUE→ ; #¬Names→∈#ASSERT₄-change-world)

open import pure(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-TPURE→ ; #⇛!nv ; #¬Names-APPLY ; ¬Names→⇛!)


{-- This version relies on ASSERT₂, which is defined in terms of BOOL,
 -- but a similar result could be obained using QTBOOL instead.
 --}

LPO : Term
LPO = PI NAT!→BOOL₀! (SQUASH (UNION! (SUM! NAT! (ASSERT₄ (APPLY (VAR 1) (VAR 0))))
                                     (PI NAT! (NEG (ASSERT₄ (APPLY (VAR 1) (VAR 0)))))))


#LPO : CTerm
#LPO = ct LPO c
  where
    c : # LPO
    c = refl



#[0]LPO-left : CTerm0
#[0]LPO-left = #[0]SUM! #[0]NAT! (#[1]ASSERT₄ (#[1]APPLY #[1]VAR1 #[1]VAR0))


#[0]LPO-right : CTerm0
#[0]LPO-right = #[0]PI #[0]NAT! (#[1]NEG (#[1]ASSERT₄ (#[1]APPLY #[1]VAR1 #[1]VAR0)))


#LPO-left : CTerm → CTerm
#LPO-left = #SUM-ASSERT₅


#LPO-right : CTerm → CTerm
#LPO-right = #PI-NEG-ASSERT₄


#LPO-PI : CTerm
#LPO-PI = #PI #NAT!→BOOL₀! (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right))


#LPO≡#PI : #LPO ≡ #LPO-PI
#LPO≡#PI = CTerm≡ refl



sub0-squash-union-LPO : (a : CTerm) → sub0 a (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right))
                                    ≡ #SQUASH (#UNION! (#LPO-left a) (#LPO-right a))
sub0-squash-union-LPO a =
  ≡sub0-#[0]SQUASH a (#[0]UNION! #[0]LPO-left #[0]LPO-right) (#UNION! (#LPO-left a) (#LPO-right a))
                   (CTerm≡ (≡UNION! (≡SUM! refl (≡ASSERT₄ (→≡APPLY e refl))) (≡PI refl (≡NEG (≡ASSERT₄ (→≡APPLY e refl))))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl



isTypeLPO-PI : (w : 𝕎·) (n : ℕ) → isType n w #LPO-PI
isTypeLPO-PI w n =
  eqTypesPI← {w} {n}
              {#NAT!→BOOL₀!} {#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)}
              {#NAT!→BOOL₀!} {#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)}
              (λ w' e → isType-#NAT!→BOOL₀! w' n)
              aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL₀! a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)))
                                        (sub0 a₂ (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right))))
    aw w' e a₁ a₂ eqb rewrite sub0-squash-union-LPO a₁ | sub0-squash-union-LPO a₂ = eqt
      where
        eqt1 : equalTypes n w' (#LPO-left a₁) (#LPO-left a₂)
        eqt1 = →equalTypes-#SUM-ASSERT₅ eqb

        eqt2 : equalTypes n w' (#LPO-right a₁) (#LPO-right a₂)
        eqt2 = →equalTypes-#PI-NEG-ASSERT₄ eqb

        eqt : equalTypes n w' (#SQUASH (#UNION! (#LPO-left a₁) (#LPO-right a₁))) (#SQUASH (#UNION! (#LPO-left a₂) (#LPO-right a₂)))
        eqt = eqTypesSQUASH← (eqTypesUNION!← eqt1 eqt2)



isTypeLPO : (w : 𝕎·) (n : ℕ) → isType n w #LPO
isTypeLPO w n rewrite #LPO≡#PI = isTypeLPO-PI w n


isTypeNegLPO : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #LPO)
isTypeNegLPO w n = eqTypesNEG← (isTypeLPO w n)


fun-equalInType-SQUASH-UNION! : {n : ℕ} {w : 𝕎·} {a b c d u v : CTerm}
                              → isType n w c
                              → isType n w d
                              → ∀𝕎 w (λ w' _ → inhType n w' a → inhType n w' c)
                              → ∀𝕎 w (λ w' _ → inhType n w' b → inhType n w' d)
                              → equalInType n w (#SQUASH (#UNION! a b)) u v
                              → equalInType n w (#SQUASH (#UNION! c d)) #AX #AX
fun-equalInType-SQUASH-UNION! {n} {w} {a} {b} {c} {d} {u} {v} istc istd imp1 imp2 eqi =
  →equalInType-SQUASH (Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ eqi)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType n w' (#UNION! a b) → □· w' (λ w'' e'' → (z : w ⊑· w'') → inhType n w'' (#UNION! c d)))
    aw1 w1 e1 (t , eqj) = Mod.∀𝕎-□Func M aw2 (equalInType-UNION!→ eqj)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → UNIONeq! (equalInType n w' a) (equalInType n w' b) w' t t
                             → (z : w ⊑· w') → inhType n w' (#UNION! c d))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , eqk)) z = #INL (fst (imp1 w2 z (x , equalInType-refl eqk))) , eql
          where
            eql : ∈Type n w2 (#UNION! c d) (#INL (fst (imp1 w2 z (x , equalInType-refl eqk))))
            eql = equalInType-UNION!
                    (eqTypes-mon (uni n) istc w2 z)
                    (eqTypes-mon (uni n) istd w2 z)
                    (Mod.∀𝕎-□ M λ w3 e3 →
                      fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                      fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                      inj₁ (#⇛!-refl {w3} {#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))} ,
                            #⇛!-refl {w3} {#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))} ,
                            equalInType-mon (snd (imp1 w2 z (x , equalInType-refl eqk))) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , eqk)) z = #INR (fst (imp2 w2 z (x , equalInType-refl eqk))) , eqr
          where
            eqr : ∈Type n w2 (#UNION! c d) (#INR (fst (imp2 w2 z (x , equalInType-refl eqk))))
            eqr = equalInType-UNION!
                    (eqTypes-mon (uni n) istc w2 z)
                    (eqTypes-mon (uni n) istd w2 z)
                    (Mod.∀𝕎-□ M λ w3 e3 →
                      fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                      fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                      inj₂ (#⇛!-refl {w3} {#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))} ,
                            #⇛!-refl {w3} {#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))} ,
                            equalInType-mon (snd (imp2 w2 z (x , equalInType-refl eqk))) w3 e3))


equalInType-SQUASH-UNION!→ : {i : ℕ} {w : 𝕎·} {a b u v : CTerm}
                           → equalInType i w (#SQUASH (#UNION! a (#NEG b))) u v
                           → □· w (λ w' _ → inhType i w' a ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' b))
equalInType-SQUASH-UNION!→ {i} {w} {a} {b} {u} {v} eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 h3)
  where
    h1 : □· w (λ w' _ → Σ CTerm (λ t → equalInType i w' (#UNION! a (#NEG b)) t t))
    h1 = equalInType-SQUASH→ eqi

    h2 : □· w (λ w' _ → Σ CTerm (λ t → □· w' (λ w'' _ → UNIONeq! (equalInType i w'' a) (equalInType i w'' (#NEG b)) w'' t t)))
    h2 = Mod.∀𝕎-□Func M (λ w' e (t , eqj) → t , equalInType-UNION!→ eqj) h1

    h3 : □· w (λ w' _ → Σ CTerm (λ t → □· w' (λ w'' _ → UNIONeq! (equalInType i w'' a)
                                                                 (λ x y →  ∀𝕎 w'' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂))
                                                                 w'' t t)))
    h3 = Mod.∀𝕎-□Func M (λ w1 e1 (t , eqt) → t , Mod.∀𝕎-□Func M (λ { w3 e3 (x , y , inj₁ (c₁ , c₂ , z)) → x , y , inj₁ (c₁ , c₂ , z) ;
                                                                     w3 e3 (x , y , inj₂ (c₁ , c₂ , z)) → x , y , inj₂ (c₁ , c₂ , equalInType-NEG→ z) }) eqt) h2

    aw1 : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → □· w' (λ w'' _ → UNIONeq! (equalInType i w'' a)
                                                                   (λ x y → ∀𝕎 w'' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂))
                                                                   w'' t t))
                        → □· w' (↑wPred' (λ w'' e →  inhType i w'' a ⊎ ∀𝕎 w'' (λ w''' _ → ¬ inhType i w''' b)) e'))
    aw1 w1 e1 (t , j) = Mod.□-idem M (Mod.∀𝕎-□Func M aw2 j)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → UNIONeq! (equalInType i w' a) (λ x y → ∀𝕎 w' (λ w''' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w''' b a₁ a₂)) w' t t
                             → □· w' (↑wPred' (λ w'' e → ↑wPred' (λ w''' e₁ → inhType i w''' a ⊎ ∀𝕎 w''' (λ w'''' _ → ¬ inhType i w'''' b)) e1 w'' e) e'))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , z)) = Mod.∀𝕎-□ M (λ w3 e3 x₁ x₂ → inj₁ (x , equalInType-mon (equalInType-refl z) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , z)) = Mod.∀𝕎-□ M (λ w3 e3 x₁ x₂ → inj₂ (λ w4 e4 (t , h) → z w4 (⊑-trans· e3 e4) t t h))


sq-dec! : CTerm → CTerm
sq-dec! t = #SQUASH (#UNION! t (#NEG t))


¬-dec!-Σchoice : (w : 𝕎·) (i : ℕ)
               → ¬ equalInType i (startNewChoice Resℂ w) (sq-dec! (#Σchoice (newChoice· w) ℂ₁·)) #AX #AX
¬-dec!-Σchoice w1 i eqi = concl h3
  where
    name : Name
    name = newChoice· w1

    r : Res
    r = Resℂ

    w2 : 𝕎·
    w2 = startChoice· name r w1

    e2 : w1 ⊑· w2
    e2 = startNewChoice⊏ r w1

    k1 : ℂ·
    k1 = ℂ₁· -- This has to be different from r's default value

    dks : (w : 𝕎·) → ¬ ∼C! w (ℂ→C· (Res.def r)) (ℂ→C· k1)
    dks = ¬∼ℂ₀₁·

    h1 : equalInType i w2 (#SQUASH (#UNION! (#Σchoice name k1) (#NEG (#Σchoice name k1)))) #AX #AX
    h1 = eqi

    h2 : □· w2 (λ w' _ → inhType i w' (#Σchoice name k1) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#Σchoice name k1)))
    h2 = equalInType-SQUASH-UNION!→ h1

    oc1 : onlyℂ∈𝕎 (Res.def r) name w2
    oc1 n = getChoice-startNewChoice n r w1

    comp1 : compatible· name w2 r
    comp1 = startNewChoiceCompatible r w1

    fb1 : freezable· name w2
    fb1 = freezableStart· r w1

    -- We follow the choice
    w3 : 𝕎·
    w3 = fst (followChoice· name h2 oc1 comp1 fb1)

    e3 : w2 ⊑· w3
    e3 = fst (snd (followChoice· name h2 oc1 comp1 fb1))

    oc2 : onlyℂ∈𝕎 (Res.def r) name w3
    oc2 = fst (snd (snd (followChoice· name h2 oc1 comp1 fb1)))

    comp2 : compatible· name w3 r
    comp2 = fst (snd (snd (snd (followChoice· name h2 oc1 comp1 fb1))))

    fb2 : freezable· name w3
    fb2 = fst (snd (snd (snd (snd (followChoice· name h2 oc1 comp1 fb1)))))

    h3 : inhType i w3 (#Σchoice name k1) ⊎ ∀𝕎 w3 (λ w'' _ → ¬ inhType i w'' (#Σchoice name k1))
    h3 = snd (snd (snd (snd (snd (followChoice· name h2 oc1 comp1 fb1)))))

    -- 1st injection: proved by ¬equalInType-#Σchoice
    -- For this it is enough to be able to make a choice different from k1 forever, for example choosing 0 forever

    -- 2nd injection: proved by ¬∀𝕎¬equalInType-#Σchoice
    -- This is where we make another choice than the default choice

    -- conclusion
    concl : (inhType i w3 (#Σchoice name k1) ⊎ ∀𝕎 w3 (λ w'' _ → ¬ inhType i w'' (#Σchoice name k1)))
            → ⊥
    concl (inj₁ eqi) = ¬equalInType-#Σchoice i w3 Resℂ name isValueℂ₀· isValueℂ₁· dks oc2 comp2 fb2 eqi
    concl (inj₂ aw) = ¬∀𝕎¬equalInType-#Σchoice i w3 name k1 sat-ℂ₁ comp2 fb2 aw


#PI-NEG-ASSERT₄→#Σchoice : Bool₀!ℂ CB → {n : ℕ} {w : 𝕎·} {name : Name}
                         → compatible· name w Resℂ
                         → Σ ℕ (λ n → ·ᵣ Resℂ n ℂ₁·)
                         → inhType n w (#PI-NEG-ASSERT₄ (#CS name))
                         → inhType n w (#NEG (#Σchoice name ℂ₁·))
#PI-NEG-ASSERT₄→#Σchoice bcb {n} {w} {name} comp sat (f , inh) =
  #lamAX , equalInType-NEG aw1 aw2
  where
    aw0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]NEG (#[0]ASSERT₄ (#[0]APPLY (#[0]CS name) #[0]VAR))))
                                          (#APPLY f a₁)
                                          (#APPLY f a₂))
    aw0 = snd (snd (equalInType-PI→ {n} {w} {#NAT!} {#[0]NEG (#[0]ASSERT₄ (#[0]APPLY (#[0]CS name) #[0]VAR))} inh))

    aw1 : isType n w (#Σchoice name ℂ₁·)
    aw1 = equalInType-#Σchoice w name ℂ₁· comp sat

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#Σchoice name ℂ₁·) a₁ a₂)
    aw2 w1 e1 p₁ p₂ eqi = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw3 h1))
      where
        aw3 : ∀𝕎 w1 (λ w' e' → SUMeq! (equalInType n w' #NAT!)
                                      (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)))
                                      w' p₁ p₂
                             → Lift (lsuc L) ⊥)
        aw3 w2 e2 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = lift (eqi3 eqi4)
          where
            eqi1 : equalInType n w2 (#EQ (#APPLY (#CS name) a₁) Cℂ₁ Typeℂ₀₁·) b₁ b₂
            eqi1 = ≡CTerm→equalInType (sub0-#Σchoice-body≡ a₁ name ℂ₁·) eb

            eqi2 : equalInType n w2 (#NEG (#ASSERT₄ (#APPLY (#CS name) a₁))) (#APPLY f a₁) (#APPLY f a₂)
            eqi2 = ≡CTerm→equalInType (sub0-NEG-ASSERT₄-APPLY a₁ (#CS name)) (aw0 w2 (⊑-trans· e1 e2) a₁ a₂ ea)

            eqi3 : ¬ equalInType n w2 (#ASSERT₄ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi3 = equalInType-NEG→ eqi2 w2 (⊑-refl· _) b₁ b₂

            eqi4 : equalInType n w2 (#ASSERT₄ (#APPLY (#CS name) a₁)) b₁ b₂
            eqi4 = ≡CTerm→equalInType (trans (≡#EQ {#APPLY (#CS name) a₁} refl (snd (snd bcb)) (fst bcb))
                                              (sym (#ASSERT₄≡ (#APPLY (#CS name) a₁))))
                                       eqi1

        h0 : equalInType n w1 (#SUM! #NAT! (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁)) p₁ p₂
        h0 = ≡CTerm→equalInType (#Σchoice≡ name ℂ₁·) eqi

        h1 : □· w1 (λ w' _ → SUMeq! (equalInType n w' #NAT!) (λ a b ea → equalInType n w' (sub0 a (#[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁))) w' p₁ p₂)
        h1 = equalInType-SUM!→ {B = #[0]EQ (#[0]APPLY (#[0]CS name) #[0]VAR) ⌞ Cℂ₁ ⌟ #[0]Typeℂ₀₁} h0


-- Assuming that our choices are Bools
¬LPO : Bool₀!ℂ CB → (w : 𝕎·) → member w (#NEG #LPO) #lamAX
¬LPO bcb w = n , equalInType-NEG (isTypeLPO w n) aw1
  where
    n : ℕ
    n = 1

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' #LPO a₁ a₂)
    aw1 w1 e1 F G ea =
      h (fun-equalInType-SQUASH-UNION! (equalInType-#Σchoice w2 name ℂ₁· comp1 (0 , sat-ℂ₁ 0))
                                       (eqTypesNEG← (equalInType-#Σchoice w2 name ℂ₁· comp1 (0 , sat-ℂ₁ 0)))
                                       imp1
                                       imp2
                                       h1)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→BOOL₀! f g
                             → equalInType n w' (sub0 f (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right))) (#APPLY F f) (#APPLY G g))
        aw2 = snd (snd (equalInType-PI→ {n} {w1} {#NAT!→BOOL₀!} {#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)} ea))

        aw3 : ∀𝕎 w1 (λ w' _ → (f g : CTerm) → equalInType n w' #NAT!→BOOL₀! f g
                             → equalInType n w' (#SQUASH (#UNION! (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G g))
        aw3 w' e f g ex = ≡CTerm→equalInType (sub0-squash-union-LPO f) (aw2 w' e f g ex)

        name : Name
        name = newChoice· w1

        w2 : 𝕎·
        w2 = startNewChoice Resℂ w1

        e2 : w1 ⊑· w2
        e2 = startNewChoice⊏ Resℂ w1

        comp1 : compatible· name w2 Resℂ
        comp1 = startNewChoiceCompatible Resℂ w1

        h : ¬ equalInType n w2 (sq-dec! (#Σchoice name ℂ₁·)) #AX #AX
        h = ¬-dec!-Σchoice w1 n

        f : CTerm
        f = #CS name

        eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType n w' #BOOL₀! (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
        eqf2 w' e m = ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! n w' m))

        eqf1 : ∈Type n w2 #NAT!→BOOL₀! f
        eqf1 = →equalInType-CS-NAT!→BOOL₀! eqf2

        h1 : equalInType n w2 (#SQUASH (#UNION! (#LPO-left f) (#LPO-right f))) (#APPLY F f) (#APPLY G f)
        h1 = aw3 w2 e2 f f eqf1

        imp1 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-left f) → inhType n w' (#Σchoice name ℂ₁·))
        imp1 w3 e3 inh = #SUM-ASSERT₅→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh

        imp2 : ∀𝕎 w2 (λ w' _ → inhType n w' (#LPO-right f) → inhType n w' (#NEG (#Σchoice name ℂ₁·)))
        imp2 w3 e3 inh = #PI-NEG-ASSERT₄→#Σchoice bcb (⊑-compatible· e3 comp1) (0 , sat-ℂ₁ 0) inh


-- LPO's body
#LPOb : CTerm → CTerm → CTerm
#LPOb f g = #SQUASH (#UNION! (#LPO-left f) (#LPO-right g))


-- pure version of LPO
#LPOp : CTerm
#LPOp = #PI (#TPURE #NAT!→BOOL₀!) (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right))


#⇛!-pres-equalTypes-LPOb : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                         → equalInType i w #NAT!→BOOL₀! a₁ a₂
                         → a₁ #⇛! b₁ at w
                         → a₂ #⇛! b₂ at w
                         → equalTypes i w (#LPOb b₁ b₂) (#LPOb a₁ a₂)
#⇛!-pres-equalTypes-LPOb i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesSQUASH← (eqTypesUNION!← (→equalTypes-#SUM-ASSERT₅
                                   {i} {w} {b₁} {a₁}
                                   (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁}
                                     c₁ (#⇛!-refl {w} {a₁})
                                     (equalInType-refl a∈)))
                                 (→equalTypes-#PI-NEG-ASSERT₄
                                   {i} {w} {b₂} {a₂}
                                   (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₂} {b₂} {a₂} {a₂}
                                     c₂ (#⇛!-refl {w} {a₂})
                                     (equalInType-refl (equalInType-sym a∈)))))


#⇛!-pres-equalInType-LPOb : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ u₁ u₂ : CTerm)
                          → equalInType i w #NAT!→BOOL₀! a₁ a₂
                          → a₁ #⇛! b₁ at w
                          → a₂ #⇛! b₂ at w
                          → #isValue b₁
                          → #isValue b₂
                          → equalInType i w (#LPOb b₁ b₂) #AX #AX
                          → equalInType i w (#LPOb a₁ a₂) (#APPLY #lamAX u₁) (#APPLY #lamAX u₂)
#⇛!-pres-equalInType-LPOb i w a₁ a₂ b₁ b₂ u₁ u₂ a∈ c₁ c₂ isv₁ isv₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {#APPLY #lamAX u₁} {#AX} {#APPLY #lamAX u₂} {#AX}
    (λ w1 e1 → lift (1 , refl))
    (λ w1 e1 → lift (1 , refl))
    (equalTypes→equalInType (#⇛!-pres-equalTypes-LPOb i w a₁ a₂ b₁ b₂ a∈ c₁ c₂) b∈)


LPO-pure : (n : ℕ) (w : 𝕎·) → ∈Type n w #LPOp #lamAX
LPO-pure n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL₀!}
    {#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)}
    (λ w1 e1 → isType-#TPURE-NAT!→BOOL₀! w1 n)
    p1 p2
  where
  p1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀!) a₁ a₂
                    → equalTypes n w'
                                 (sub0 a₁ (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)))
                                 (sub0 a₂ (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right))))
  p1 w1 e1 f₁ f₂ f∈ =
    →≡equalTypes
      (sym (sub0-squash-union-LPO f₁))
      (sym (sub0-squash-union-LPO f₂))
        (eqTypesSQUASH← (eqTypesUNION!← (→equalTypes-#SUM-ASSERT₅ (equalInType-TPURE→ f∈))
                                        (→equalTypes-#PI-NEG-ASSERT₄ (equalInType-TPURE→ f∈))))

  p2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀!) a₁ a₂
                    → equalInType n w'
                                  (sub0 a₁ (#[0]SQUASH (#[0]UNION! #[0]LPO-left #[0]LPO-right)))
                                  (#APPLY #lamAX a₁) (#APPLY #lamAX a₂))
  p2 w1 e1 f₁ f₂ f∈ =
    →≡equalInType
      (sym (sub0-squash-union-LPO f₁))
      (equalInType-local
          (∀𝕎-□Func2 aw1
            (equalInType-TPURE-NAT!→BOOL₀!ₗ n w1 f₁ f₂ f∈)
            (equalInType-TPURE-NAT!→BOOL₀!ᵣ n w1 f₁ f₂ f∈)))
    where
    aw1 : ∀𝕎 w1 (λ w' e' → #⇛!nv f₁ w'
                         → #⇛!nv f₂ w'
                         → equalInType n w' (#LPOb f₁ f₁) (#APPLY #lamAX f₁) (#APPLY #lamAX f₂))
    aw1 w2 e2 (g₁ , comp₁ , nng₁ , neg₁ , isvg₁) (g₂ , comp₂ , nng₂ , neg₂ , isvg₂) =
      #⇛!-pres-equalInType-LPOb n w2 f₁ f₁ g₁ g₁ f₁ f₂
        (equalInType-mon (equalInType-refl (equalInType-TPURE→ f∈)) w2 e2)
        comp₁ comp₁ isvg₁ isvg₁
        (→equalInType-SQUASH (Mod.∀𝕎-□ M aw2))
      where
      aw2 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#UNION! (#LPO-left g₁) (#LPO-right g₁)) t t))
      aw2 w3 e3 = cc (EM {inhType n w3 (#SUM-ASSERT₅ g₁)})
        where
        g∈ : equalInType n w3 (#TPURE #NAT!→BOOL₀!) g₁ g₂
        g∈ = equalInType-#⇛-LR
               {n} {w3} {#TPURE #NAT!→BOOL₀!} {f₁} {g₁} {f₂} {g₂}
               (∀𝕎-mon e3 comp₁) (∀𝕎-mon e3 comp₂) (equalInType-mon f∈ w3 (⊑-trans· e2 e3))

        cc : Dec (inhType n w3 (#SUM-ASSERT₅ g₁))
           → Σ CTerm (λ t → equalInType n w3 (#UNION! (#LPO-left g₁) (#LPO-right g₁)) t t)
        cc (yes (t , p)) =
          #INL t ,
          equalInType-UNION! (→equalTypes-#SUM-ASSERT₅ (equalInType-TPURE→ (equalInType-refl g∈)))
                             (→equalTypes-#PI-NEG-ASSERT₄ (equalInType-TPURE→ (equalInType-refl g∈)))
                             (Mod.∀𝕎-□ M aw3)
            where
            aw3 : ∀𝕎 w3 (λ w' _ → UNIONeq! (equalInType n w' (#SUM-ASSERT₅ g₁))
                                           (equalInType n w' (#PI-NEG-ASSERT₄ g₁))
                                           w' (#INL t) (#INL t))
            aw3 w4 e4 =
              t , t ,
              inj₁ (#⇛!-refl {w4} {#INL t} ,
                    #⇛!-refl {w4} {#INL t} ,
                    equalInType-mon p w4 e4)
        cc (no p) =
          #INR #AX ,
          equalInType-UNION! (→equalTypes-#SUM-ASSERT₅ (equalInType-TPURE→ (equalInType-refl g∈)))
                             (→equalTypes-#PI-NEG-ASSERT₄ (equalInType-TPURE→ (equalInType-refl g∈)))
                             (Mod.∀𝕎-□ M aw3)
            where
            aw3 : ∀𝕎 w3 (λ w' _ → UNIONeq! (equalInType n w' (#SUM-ASSERT₅ g₁))
                                           (equalInType n w' (#PI-NEG-ASSERT₄ g₁))
                                           w' (#INR #AX) (#INR #AX))
            aw3 w4 e4 =
              #AX , #AX ,
              inj₂ (#⇛!-refl {w4} {#INR #AX} ,
                    #⇛!-refl {w4} {#INR #AX} ,
                    equalInType-PI
                      {B = #[0]NEG (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR))}
                      (λ w' e → isTypeNAT!)
                      aw4 aw5)
              where
              aw4 : ∀𝕎 w4 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR))))
                                         (sub0 b (#[0]NEG (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR)))))
              aw4 w' e a b ea rewrite sub0-NEG-ASSERT₄-APPLY a g₁ | sub0-NEG-ASSERT₄-APPLY b g₁ = aw5
                where
                eqb : equalInType n w' #BOOL₀! (#APPLY g₁ a) (#APPLY g₁ b)
                eqb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-TPURE→ (equalInType-refl g∈)))
                                       w' (⊑-trans· e4 e) a b ea

                aw5 : equalTypes n w' (#NEG (#ASSERT₄ (#APPLY g₁ a))) (#NEG (#ASSERT₄ (#APPLY g₁ b)))
                aw5 = eqTypesNEG← (equalInType-BOOL₀!→equalTypes-ASSERT₄ eqb)

              aw5 : ∀𝕎 w4 (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                                  → equalInType n w' (sub0 a₁ (#[0]NEG (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR))))
                                                (#APPLY #AX a₁) (#APPLY #AX a₂))
              aw5 w5 e5 n₁ n₂ n∈ =
                →≡equalInType
                  (sym (sub0-NEG-ASSERT₄-APPLY n₁ g₁))
                  (equalInType-NEG
                    (equalInType-BOOL₀!→equalTypes-ASSERT₄ eqb)
                    aw6)
                where
                eqb : equalInType n w5 #BOOL₀! (#APPLY g₁ n₁) (#APPLY g₁ n₁)
                eqb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-TPURE→ (equalInType-refl g∈)))
                                       w5 (⊑-trans· e4 e5) n₁ n₁ (equalInType-refl n∈)

                aw6 : ∀𝕎 w5 (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#ASSERT₄ (#APPLY g₁ n₁)) a₁ a₂)
                aw6 w6 e6 a₁ a₂ a∈ =
                  -- extract first some nums from n₁ and n₂
                  lower {0ℓ} {lsuc(L)}
                        (Mod.□-const M (Mod.∀𝕎-□Func M aw7 ((equalInType-NAT!→ n w6 n₁ n₂ (equalInType-mon n∈ w6 e6)))))
                  where
                  aw7 : ∀𝕎 w6 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → Lift (lsuc L) ⊥)
                  aw7 w7 e7 (k , ck₁ , ck₂) =
                    lift (p (#PAIR (#NUM k) a₁ ,
                             equalInType-SUM!
                               {B = #[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR)}
                               (λ w' e → isTypeNAT!)
                               aw8
                               (Mod.∀𝕎-□ M aw9)))
                    where
                    aw8 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR)))
                                                          (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR))))
                    aw8 w' e a b ea rewrite sub0-ASSERT₄-APPLY a g₁ | sub0-ASSERT₄-APPLY b g₁ =
                      equalInType-BOOL₀!→equalTypes-ASSERT₄
                        (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-TPURE→ (equalInType-refl g∈)))
                                          w' e a b ea)

                    aw9 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType n w' #NAT!)
                                                 (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ g₁ ⌟ #[0]VAR))))
                                                 w' (#PAIR (#NUM k) a₁) (#PAIR (#NUM k) a₁))
                    aw9 w3a e3a =
                      #NUM k , #NUM k , a₁ , a₁ ,
                      NUM-equalInType-NAT! n w3a k ,
                      #⇛!-refl {w3a} {#PAIR (#NUM k) a₁} ,
                      #⇛!-refl {w3a} {#PAIR (#NUM k) a₁} ,
                      ≡CTerm→equalInType
                        (sym (sub0-ASSERT₄-APPLY (#NUM k) g₁))
                        (#¬Names→∈#ASSERT₄-change-world
                          n w7 w3a (#APPLY g₁ (#NUM k)) a₁ a₁
                          (#¬Names-APPLY {g₁} {#NUM k} nng₁ refl)
                          (equalTypes→equalInType
                            (equalInType-BOOL₀!→equalTypes-ASSERT₄
                            {n} {w7} {#APPLY g₁ n₁} {#APPLY g₁ (#NUM k)}
                            (equalInType-FUN→
                              (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-TPURE→ (equalInType-refl g∈)))
                              w7 (⊑-trans· e4 (⊑-trans· e5 (⊑-trans· e6 e7))) n₁ (#NUM k)
                              (→equalInType-NAT! n w7 n₁ (#NUM k) (Mod.∀𝕎-□ M a10))))
                            (equalInType-refl (equalInType-mon a∈ w7 e7))))
                      where
                      a10 : ∀𝕎 w7 (λ w' _ → #⇛!sameℕ w' n₁ (#NUM k))
                      a10 w8 e8 = k , ∀𝕎-mon e8 ck₁ , #⇛!-refl {w8} {#NUM k}

\end{code}[hide]
