\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --lossy-unification #-}
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
open import Axiom.ExcludedMiddle


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
--open import choiceBar
open import encode


module barContP10 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                  (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                  (X : ChoiceExt W C)
                  (N : NewChoice {L} W C K G)
                  (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                  (EM : ExcludedMiddle (lsuc(L)))
                  (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC) using (≡APPLY ; ≡SUBSING ; ≡EQ ; upd)
--open import terms4(W)(C)(K)(G)(X)(N)(EC)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
--open import terms6(W)(C)(K)(G)(X)(N)(EC)
--open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC) using (#APPLY2 ; #⇛-trans ; #INL¬≡INR ; #[2]shiftUp0 ; #[1]shiftUp0 ; #[0]shiftUp0 ; #[2]APPLY ; #[2]VAR2 ; #[2]VAR0)
open import terms9(W)(C)(K)(G)(X)(N)(EC) using (#BAIRE! ; BAIRE!)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇛-refl)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-trans ; →equalInTypeSUBSING)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→equalInType-NAT! ; equalInType-W→)
--open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#shiftNameUp) -- (#upd ; #force ; equalInType-force)
--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇓sameℕ)
--open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (steps-sat-isHighestℕ ; ¬Names→updCtxt)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-upd-force)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (isType-BAIRE→NAT)
--open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (isHighestℕ≤)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (isType-IndBarB ; equalTypes-IndBarC ; #INIT ; #⇛!-NUM-type)
--open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (seq2list ; mseq∈baire)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (INIT)
--open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (#FunBarP ; FunBarP ; sem)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (follow ; #follow ; weq→follow-NATeq ; #tab ; #BAIRE!≡)
open import barContP8(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (follow-NUM-ETA ; type-#⇛-NUM)
open import barContP9(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (semCond ; type-#⇛-NUM→!)


NAT→T : Term → Term
NAT→T T = FUN NAT T


NAT→!T : Term → Term
NAT→!T T = FUN NAT (NOWRITEMOD T)


#NAT→!T : CTerm → CTerm
#NAT→!T T = #FUN #NAT (#NOWRITEMOD T)


#[0]NOWRITEMOD : CTerm0 → CTerm0
#[0]NOWRITEMOD t = ct0 (NOWRITEMOD ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] NOWRITEMOD ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm0.closed t


#[1]NOWRITEMOD : CTerm1 → CTerm1
#[1]NOWRITEMOD t = ct1 (NOWRITEMOD ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] NOWRITEMOD ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm1.closed t


#[0]NOREADMOD : CTerm0 → CTerm0
#[0]NOREADMOD t = ct0 (NOREADMOD ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] NOREADMOD ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm0.closed t


#[1]NOREADMOD : CTerm1 → CTerm1
#[1]NOREADMOD t = ct1 (NOREADMOD ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] NOREADMOD ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm1.closed t


#[0]NAT→!T : CTerm → CTerm0
#[0]NAT→!T T = #[0]FUN #[0]NAT (#[0]NOWRITEMOD ⌞ T ⌟)


#[1]FUN : CTerm1 → CTerm1 → CTerm1
#[1]FUN a b = ct1 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[1]NAT→!T : CTerm → CTerm1
#[1]NAT→!T T = #[1]FUN #[1]NAT (#[1]NOWRITEMOD ⌞ T ⌟)


contDiag : Term → Term
contDiag T =
  PI (FunBarP T)
     (SUBSING
       (SUM (IndBar T) (PI (FUN NAT (NOWRITEMOD T)) (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT))))


#[2]follow010 : CTerm2
#[2]follow010 = ct2 (follow (VAR 0) (VAR 1) 0) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] (follow (VAR 0) (VAR 1) 0)
    c = refl


#[0]WT₀ : CTerm0 → CTerm1 → CTerm0
#[0]WT₀ a b = ct0 (WT₀ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] WT₀ ⌜ a ⌝ ⌜ b ⌝
    c rewrite ++[] (lowerVars (fvars ⌜ b ⌝)) =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
           (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))


#[1]PI : CTerm1 → CTerm2 → CTerm1
#[1]PI a b = ct1 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[0]UNION₀ : CTerm0 → CTerm0 → CTerm0
#[0]UNION₀ a b = #[0]NOREADMOD (#[0]UNION a b)


#[0]UNION₀! : CTerm0 → CTerm0 → CTerm0
#[0]UNION₀! a b = #[0]NOWRITEMOD (#[0]UNION₀ a b)


#[0]UNIT : CTerm0
#[0]UNIT = ct0 UNIT refl


#[0]IndBarB : CTerm0
#[0]IndBarB = #[0]UNION₀! #[0]NAT #[0]UNIT


#[1]DECIDE : CTerm1 → CTerm2 → CTerm2 → CTerm1
#[1]DECIDE a b c = ct1 (DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : #[ 0 ∷ [ 1 ] ] DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d = ⊆→⊆?
          {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝) ++ lowerVars (fvars ⌜ c ⌝)}
          {0 ∷ [ 1 ]}
          (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                (⊆++ (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b)))
                      (lowerVars-fvars-[0,1,2] {fvars ⌜ c ⌝} (⊆?→⊆ (CTerm2.closed c)))))


#[2]VOID : CTerm2
#[2]VOID = ct2 VOID c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] VOID
    c = refl


#[0]IndBarC : CTerm → CTerm1
#[0]IndBarC T = #[1]DECIDE #[1]VAR0 #[2]VOID ⌞ #NOWRITEMOD T ⌟


#[0]IndBar : CTerm → CTerm0
#[0]IndBar T = #[0]WT₀ #[0]IndBarB (#[0]IndBarC T)


#[2]EQ : CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]EQ a b c = ct2 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ 1 ∷ [ 2 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ [ 2 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                      (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b))
                            (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed c))))


#[2]NAT : CTerm2
#[2]NAT = ct2 NAT refl


#contDiag : CTerm → CTerm
#contDiag T =
  #PI (#FunBarP T)
      (#[0]SUBSING
         (#[0]SUM (#[0]IndBar T) (#[1]PI (#[1]NAT→!T T) (#[2]EQ (#[2]APPLY #[2]VAR2 #[2]VAR0) (#[2]follow010) #[2]NAT))))

{-- ct (contDiag ⌜ T ⌝) c
  where
    c : # contDiag ⌜ T ⌝
    c rewrite #shiftUp 0 T | CTerm.closed T = refl
--}


-- sanity check
⌜#contDiag≡⌝ : (T : CTerm) → ⌜ #contDiag T ⌝ ≡ contDiag ⌜ T ⌝
⌜#contDiag≡⌝ T = refl


contDiagExt : Term
contDiagExt =
  LAMBDA (PAIR (APPLY2 (loop (VAR 0)) (NUM 0) INIT) lamAX)


#contDiagExt : CTerm
#contDiagExt = ct contDiagExt c
  where
    c : # contDiagExt
    c = refl


#contDiagExt⇛ : (F : CTerm) (w : 𝕎·)
                 → #APPLY #contDiagExt F #⇛ #PAIR (#tab F 0 #INIT) #lamAX at w
#contDiagExt⇛ F w w1 e1 =
  lift (#⇓from-to→#⇓ {w1} {w1} {#APPLY #contDiagExt F} {#PAIR (#tab F 0 #INIT) #lamAX} (1 , ≡pair c refl))
  where
    c : sub ⌜ F ⌝ (PAIR (APPLY2 (loop (VAR 0)) (NUM 0) INIT) lamAX)
        ≡ ⌜ #PAIR (#tab F 0 #INIT) #lamAX ⌝
    c rewrite #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 (#shiftNameUp 0 F)
            | #shiftDown 4 (#shiftNameUp 0 F) = refl


isType-FunBar : (i : ℕ) (w : 𝕎·) (T : CTerm) → isType i w T → isType i w (#FunBar T)
isType-FunBar i w T tyt = eqTypesFUN← (eqTypesFUN← eqTypesNAT tyt) eqTypesNAT


isType-FunBarP : (i : ℕ) (w : 𝕎·) (T : CTerm) → isType i w T → isType i w (#FunBarP T)
isType-FunBarP i w T tyt = equalTypesTPURE (isType-FunBar i w T tyt)


follow1 : CTerm1
follow1 = ct1 (follow (VAR 0) (VAR 1) 0) c
  where
    c : #[ 0 ∷ [ 1 ] ] (follow (VAR 0) (VAR 1) 0)
    c = refl


follow0 : CTerm → CTerm0
follow0 W = ct0 (follow (VAR 0) ⌜ W ⌝ 0) c
  where
    c : #[ [ 0 ] ] (follow (VAR 0) ⌜ W ⌝ 0)
    c rewrite CTerm.closed W = refl


#[0]BAIRE! : CTerm0
#[0]BAIRE! = ct0 BAIRE! c
  where
    c : #[ [ 0 ] ] BAIRE!
    c = refl


#[1]EQ : CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]EQ a b T = ct1 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ T ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ T ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ T ⌝} {0 ∷ [ 1 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                     (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b))
                           (⊆?→⊆ {fvars ⌜ T ⌝} {0 ∷ [ 1 ]} (CTerm1.closed T))))


sub0-contDiag-subsing : (T F : CTerm)
                        → sub0 F (#[0]SUBSING (#[0]SUM (#[0]IndBar T) (#[1]PI (#[1]NAT→!T T) (#[2]EQ (#[2]APPLY #[2]VAR2 #[2]VAR0) (#[2]follow010) #[2]NAT))))
                           ≡ #SUBSING (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F ⌟ #[1]VAR0) follow1 #[1]NAT)))
sub0-contDiag-subsing T F = CTerm≡ e
  where
    e : sub ⌜ F ⌝ (SUBSING (SUM (IndBar ⌜ T ⌝) (PI (FUN NAT (NOWRITEMOD ⌜ T ⌝)) (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT))))
        ≡ ⌜ #SUBSING (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F ⌟ #[1]VAR0) follow1 #[1]NAT))) ⌝
    e rewrite #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F | #shiftDown 2 F
            | #shiftUp 0 T | #shiftUp 0 T
            | #subv 2 ⌜ F ⌝ ⌜ T ⌝ (CTerm.closed T)
            | #shiftDown 2 T = refl


sub0-contDiag-PI : (T F W : CTerm) (c : #[ [ 0 ] ] (PI (NAT→!T ⌜ T ⌝) (EQ (APPLY ⌜ F ⌝ (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)))
                   → sub0 W (ct0 (PI (NAT→!T ⌜ T ⌝) (EQ (APPLY ⌜ F ⌝ (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)) c)
                      ≡ #PI (#NAT→!T T) (#[0]EQ (#[0]APPLY ⌞ F ⌟ #[0]VAR) (follow0 W) #[0]NAT)
sub0-contDiag-PI T F W c = CTerm≡ e
  where
    e : ⌜ sub0 W (ct0 (PI (NAT→!T ⌜ T ⌝) (EQ (APPLY ⌜ F ⌝ (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)) c) ⌝
        ≡ ⌜ #PI (#NAT→!T T) (#[0]EQ (#[0]APPLY ⌞ F ⌟ #[0]VAR) (follow0 W) #[0]NAT) ⌝
    e rewrite #shiftUp 0 W | #shiftUp 0 W
            | #subv 1 ⌜ W ⌝ ⌜ F ⌝ (CTerm.closed F)
            | #shiftDown 1 W | #shiftDown 1 F
            | #shiftUp 0 T
            | #subv 1 ⌜ W ⌝ ⌜ T ⌝ (CTerm.closed T)
            | #shiftDown 1 T = refl


sub0-contDiag-EQ : (F W a : CTerm) (c : #[ [ 0 ] ] (EQ ⌜ #[0]APPLY ⌞ F ⌟ #[0]VAR ⌝ ⌜ follow0 W ⌝ NAT))
                   → sub0 a (ct0 (EQ ⌜ #[0]APPLY ⌞ F ⌟ #[0]VAR ⌝ ⌜ follow0 W ⌝ NAT) c)
                      ≡ #EQ (#APPLY F a) (#follow a W 0) #NAT
sub0-contDiag-EQ F W a c = CTerm≡ e
  where
    e : ⌜ sub0 a (ct0 (EQ ⌜ #[0]APPLY ⌞ F ⌟ #[0]VAR ⌝ ⌜ follow0 W ⌝ NAT) c) ⌝
        ≡ ⌜ #EQ (#APPLY F a) (#follow a W 0) #NAT ⌝
    e rewrite #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #subv 0 ⌜ a ⌝ ⌜ W ⌝ (CTerm.closed W)
            | #subv 0 ⌜ a ⌝ ⌜ F ⌝ (CTerm.closed F)
            | #shiftDown 0 F
            | #shiftDown 0 W
            | #shiftDown 0 a
            | #shiftDown 6 a = refl


isType-IndBar : (i : ℕ) (w : 𝕎·) (T : CTerm) → isType i w T → isType i w (#IndBar T)
isType-IndBar i w T tyt =
  eqTypesW₀←
    {w} {i} {#IndBarB} {#IndBarC T} {#IndBarB} {#IndBarC T}
    (isType-IndBarB i w)
    (λ w1 e1 a b eqa → equalTypes-IndBarC  i w1 T a b (eqTypes-mon (uni i) tyt w1 e1) eqa)


isType-BAIRE! : {w : 𝕎·} {i : ℕ} → isType i w #BAIRE!
isType-BAIRE! {w} {i} =
  ≡CTerm→eqTypes (sym #BAIRE!≡) (sym #BAIRE!≡) (eqTypesFUN← {w} {i} {#NAT} {#NAT!} eqTypesNAT isTypeNAT!)


APPLY-∈BAIRE!→NAT! : (i : ℕ) (w : 𝕎·) (f₁ f₂ a₁ a₂ : CTerm)
                       → equalInType i w #BAIRE! f₁ f₂
                       → equalInType i w #NAT a₁ a₂
                       → equalInType i w #NAT! (#APPLY f₁ a₁) (#APPLY f₂ a₂)
APPLY-∈BAIRE!→NAT! i w f₁ f₂ a₁ a₂ f∈ a∈ =
  equalInType-FUN→ (≡CTerm→equalInType #BAIRE!≡ f∈) w (⊑-refl· w) a₁ a₂ a∈


NAT!→NAT : (i : ℕ) (w : 𝕎·) (a b : CTerm)
            → equalInType i w #NAT! a b
            → equalInType i w #NAT a b
NAT!→NAT i w a b h = →equalInType-NAT i w a b (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w a b h))
  where
    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b → NATeq w' a b)
    aw w1 e1 (k , c1 , c2) = k , #⇛!→#⇛ {w1} {a} {#NUM k} c1 , #⇛!→#⇛ {w1} {b} {#NUM k} c2


NOWRITEMOD→T : (i : ℕ) (w : 𝕎·) (T a b : CTerm)
            → equalInType i w (#NOWRITEMOD T) a b
            → equalInType i w T a b
NOWRITEMOD→T i w T a b h =
  equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 (x , y , z) → x) (equalInTypeNOWRITEMOD→ h))


BAIRE!→BAIRE : (i : ℕ) (w : 𝕎·) (T a b : CTerm)
                → isType i w T
                → equalInType i w (#NAT→!T T) a b
                → equalInType i w (#NAT→T T) a b
BAIRE!→BAIRE i w T a b tyt h =
  equalInType-FUN eqTypesNAT tyt aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂ → equalInType i w' T (#APPLY a a₁) (#APPLY b a₂))
    aw w1 e1 a₁ a₂ ea = NOWRITEMOD→T i w1 T (#APPLY a a₁) (#APPLY b a₂) (equalInType-FUN→ h w1 e1 a₁ a₂ ea)


isType-NAT→!T : {i : ℕ} {w : 𝕎·} {T : CTerm}
                → isType i w T
                → isType i w (#NAT→!T T)
isType-NAT→!T {i} {w} {T} tyt = eqTypesFUN← eqTypesNAT (eqTypesNOWRITEMOD← tyt)


APPLY-FunBarP-BAIRE!→ : {i : ℕ} {w : 𝕎·} {T F₁ F₂ a₁ a₂ : CTerm}
                         → isType i w T
                         → equalInType i w (#FunBarP T) F₁ F₂
                         → equalInType i w (#NAT→!T T) a₁ a₂
                         → equalInType i w #NAT (#APPLY F₁ a₁) (#APPLY F₂ a₂)
APPLY-FunBarP-BAIRE!→ {i} {w} {T} {F₁} {F₂} {a₁} {a₂} tyt F∈P a∈ =
  equalInType-FUN→ F∈ w (⊑-refl· w) a₁ a₂ (BAIRE!→BAIRE i w T a₁ a₂ tyt a∈)
  where
    F∈ : equalInType i w (#FunBar T) F₁ F₂
    F∈ = equalInType-TPURE→ F∈P


→equalInType-follow∈NAT : (kb : K□) {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T W₁ W₂ a₁ a₂ : CTerm}
                            → type-#⇛!-NUM P T
                            → #⇛!-NUM-type P T
                            → equalInType i w (#IndBar T) W₁ W₂
                            → equalInType i w (#NAT→!T T) a₁ a₂
                            → equalInType i w #NAT (#follow a₁ W₁ 0) (#follow a₂ W₂ 0)
→equalInType-follow∈NAT kb {i} {w} P {T} {W₁} {W₂} {a₁} {a₂} tyn nty W∈ a∈ =
  →equalInType-NAT
    i w (#follow a₁ W₁ 0) (#follow a₂ W₂ 0)
    (Mod.∀𝕎-□Func M aw (equalInType-W₀→ kb i w #IndBarB (#IndBarC T) W₁ W₂ W∈))
  where
    aw : ∀𝕎 w (λ w' e' → weq₀ (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a (#IndBarC T))) w' W₁ W₂
                        → NATeq w' (#follow a₁ W₁ 0) (#follow a₂ W₂ 0))
    aw w1 e1 h =
      weq→follow-NATeq
        kb i w1 P T W₁ W₂ a₁ a₂ 0 tyn nty h
        (λ k → equalInType-FUN→ a∈ w1 e1 (#NUM k) (#NUM k) (NUM-equalInType-NAT i w1 k))


contDiagVal-type3 : (kb : K□) (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F₁ F₂ W₁ W₂ a₁ a₂ : CTerm)
                    → isType i w T
                    → type-#⇛!-NUM P T
                    → #⇛!-NUM-type P T
                    → equalInType i w (#FunBarP T) F₁ F₂
                    → equalInType i w (#IndBar T) W₁ W₂
                    → equalInType i w (#NAT→!T T) a₁ a₂
                    → equalTypes
                         i w
                         (#EQ (#APPLY F₁ a₁) (#follow a₁ W₁ 0) #NAT)
                         (#EQ (#APPLY F₂ a₂) (#follow a₂ W₂ 0) #NAT)
contDiagVal-type3 kb i w P T F₁ F₂ W₁ W₂ a₁ a₂ tyt tyn nty F∈ W∈ a∈ =
  eqTypesEQ←
    {_} {_} {#APPLY F₁ a₁} {#follow a₁ W₁ 0} {#APPLY F₂ a₂} {#follow a₂ W₂ 0} {#NAT} {#NAT}
    eqTypesNAT
    (APPLY-FunBarP-BAIRE!→ tyt F∈ a∈)
    (→equalInType-follow∈NAT kb {i} {w} P {T} {W₁} {W₂} {a₁} {a₂} tyn nty W∈ a∈)


contDiagVal-type2 : (kb : K□) (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F₁ F₂ W₁ W₂ : CTerm)
                    → isType i w T
                    → type-#⇛!-NUM P T
                    → #⇛!-NUM-type P T
                    → equalInType i w (#FunBarP T) F₁ F₂
                    → equalInType i w (#IndBar T) W₁ W₂
                    → equalTypes
                         i w
                         (#PI (#NAT→!T T) (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) (follow0 W₁) #[0]NAT))
                         (#PI (#NAT→!T T) (#[0]EQ (#[0]APPLY ⌞ F₂ ⌟ #[0]VAR) (follow0 W₂) #[0]NAT))
contDiagVal-type2 kb i w P T F₁ F₂ W₁ W₂ tyt tyn nty F∈ W∈ =
  eqTypesPI←
    (λ w1 e1 → isType-NAT→!T (eqTypes-mon (uni i) tyt w1 e1))
    (λ w1 e1 a₁ a₂ a∈ →
      →≡equalTypes
        (sym (sub0-contDiag-EQ F₁ W₁ a₁ _)) (sym (sub0-contDiag-EQ F₂ W₂ a₂ _))
        (contDiagVal-type3 kb i w1 P T F₁ F₂ W₁ W₂ a₁ a₂ (eqTypes-mon (uni i) tyt w1 e1) tyn nty (equalInType-mon F∈ w1 e1) (equalInType-mon W∈ w1 e1) a∈))


contDiagVal-type1 : (kb : K□) (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F₁ F₂ : CTerm)
                    → isType i w T
                    → type-#⇛!-NUM P T
                    → #⇛!-NUM-type P T
                    → equalInType i w (#FunBarP T) F₁ F₂
                    → equalTypes
                         i w
                         (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT)))
                         (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F₂ ⌟ #[1]VAR0) follow1 #[1]NAT)))
contDiagVal-type1 kb i w P T F₁ F₂ tyt tyn nty F∈ =
  eqTypesSUM←
    (λ w1 e1 → isType-IndBar i w1 T (eqTypes-mon (uni i) tyt w1 e1))
    (λ w1 e1 W₁ W₂ W∈ →
      →≡equalTypes
        (sym (sub0-contDiag-PI T F₁ W₁ _)) (sym (sub0-contDiag-PI T F₂ W₂ _))
        (contDiagVal-type2 kb i w1 P T F₁ F₂ W₁ W₂ (eqTypes-mon (uni i) tyt w1 e1) tyn nty (equalInType-mon F∈ w1 e1) W∈))


semCondEQ : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (P : ℕ → Set) (T F f : CTerm) (a b : CTerm)
            → compatible· r w Res⊤
            → P 0
            → #⇛!-NUM-type P T
            → type-#⇛-NUM P T
            → type-preserves-#⇛ T
            → isType i w T
            → ∈Type i w (#FunBarP T) F
            → ∈Type i w (#NAT→!T T) f
            → equalInType i w (#EQ (#APPLY F f) (#follow f (#tab F 0 #INIT) 0) #NAT) a b
semCondEQ kb cn can exb gc i w r P T F f a b compat p0 nty tyn prest tyt F∈P f∈ =
  equalInType-EQ
    eqTypesNAT
    (Mod.∀𝕎-□ M (λ w1 e1 → semCond kb cn can exb gc i w1 P T F f
                                     p0 nty tyn prest (eqTypes-mon (uni i) tyt w1 e1)
                                     (equalInType-mon F∈P w1 e1) (equalInType-mon f∈ w1 e1)))


semCond2 : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
          (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F₁ F₂ f : CTerm)
          → P 0
          → #⇛!-NUM-type P T
          → type-#⇛-NUM P T
          → type-preserves-#⇛ T
          → isType i w T
          → equalInType i w (#FunBarP T) F₁ F₂
          → ∈Type i w (#NAT→!T T) f
          → equalInType i w #NAT (#APPLY F₁ f) (#follow f (#tab F₂ 0 #INIT) 0)
semCond2 kb cn can exb gc i w P T F₁ F₂ f p0 nty tyn prest tyt F∈P f∈ =
  equalInType-trans eqn (semCond kb cn can exb gc i w P T F₂ f p0 nty tyn prest tyt (equalInType-refl (equalInType-sym F∈P)) f∈)
  where
    eqn : equalInType i w #NAT (#APPLY F₁ f) (#APPLY F₂ f)
    eqn = APPLY-FunBarP-BAIRE!→ tyt F∈P f∈


semCondEQ2 : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F₁ F₂ f : CTerm) (a b : CTerm)
            → P 0
            → #⇛!-NUM-type P T
            → type-#⇛-NUM P T
            → type-preserves-#⇛ T
            → isType i w T
            → equalInType i w (#FunBarP T) F₁ F₂
            → ∈Type i w (#NAT→!T T) f
            → equalInType i w (#EQ (#APPLY F₁ f) (#follow f (#tab F₂ 0 #INIT) 0) #NAT) a b
semCondEQ2 kb cn can exb gc i w P T F₁ F₂ f a b p0 nty tyn prest tyt F∈P f∈ =
  equalInType-EQ
    eqTypesNAT
    (Mod.∀𝕎-□ M (λ w1 e1 → semCond2 kb cn can exb gc i w1 P T F₁ F₂ f
                                      p0 nty tyn prest (eqTypes-mon (uni i) tyt w1 e1)
                                      (equalInType-mon F∈P w1 e1) (equalInType-mon f∈ w1 e1)))


contDiagVal1 : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
               (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F₁ F₂ : CTerm)
               → P 0
               → #⇛!-NUM-type P T
               → type-#⇛-NUM P T
               → type-preserves-#⇛ T
               → isType i w T
               → equalInType i w (#FunBarP T) F₁ F₂
               → ∈Type i w (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))) (#APPLY #contDiagExt F₂)
contDiagVal1 kb cn can exb gc i w P T F₁ F₂ p0 nty tyn prest tyt F∈ =
  equalInType-SUM
    (λ w1 e1 → isType-IndBar i w1 T (eqTypes-mon (uni i) tyt w1 e1))
    (λ w1 e1 W₁ W₂ W∈ →
      →≡equalTypes
        (sym (sub0-contDiag-PI T F₁ W₁ _)) (sym (sub0-contDiag-PI T F₁ W₂ _))
        (contDiagVal-type2 kb i w1 P T F₁ F₁ W₁ W₂ (eqTypes-mon (uni i) tyt w1 e1) (type-#⇛-NUM→! P T tyn) nty (equalInType-refl (equalInType-mon F∈ w1 e1)) W∈))
    (Mod.∀𝕎-□ M h1)
  where
    h1 : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' (#IndBar T))
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))))
                                w' (#APPLY #contDiagExt F₂) (#APPLY #contDiagExt F₂))
    h1 w1 e1 =
      #tab F₂ 0 #INIT , #tab F₂ 0 #INIT , #lamAX , #lamAX ,
      sem kb cn can exb gc i w1 P T F₂ p0 prest (type-#⇛-NUM→! P T tyn) nty (eqTypes-mon (uni i) tyt w1 e1) (equalInType-refl (equalInType-sym (equalInType-mon F∈ w1 e1))) ,
      lower (#contDiagExt⇛ F₂ w1 w1 (⊑-refl· w1)) , --#contDiagExt⇛ F₂ w1 ,
      lower (#contDiagExt⇛ F₂ w1 w1 (⊑-refl· w1)) , --#contDiagExt⇛ F₂ w1 ,
      →≡equalInType (sym (sub0-contDiag-PI T F₁ (#tab F₂ 0 #INIT) _)) h2
      where
        h2 : equalInType i w1 (#PI (#NAT→!T T) (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) (follow0 (#tab F₂ 0 #INIT)) #[0]NAT)) #lamAX #lamAX
        h2 = equalInType-PI
               (λ w2 e2 → isType-NAT→!T (eqTypes-mon (uni i) tyt w2 (⊑-trans· e1 e2)))
               (λ w2 e2 a₁ a₂ a∈ →
                 →≡equalTypes
                   (sym (sub0-contDiag-EQ F₁ (#tab F₂ 0 #INIT) a₁ _)) (sym (sub0-contDiag-EQ F₁ (#tab F₂ 0 #INIT) a₂ _))
                   (contDiagVal-type3
                     kb i w2 P T F₁ F₁ (#tab F₂ 0 #INIT) (#tab F₂ 0 #INIT) a₁ a₂
                     (eqTypes-mon (uni i) tyt w2 (⊑-trans· e1 e2)) (type-#⇛-NUM→! P T tyn) nty
                     (equalInType-refl (equalInType-mon F∈ w2 (⊑-trans· e1 e2)))
                     (sem kb cn can exb gc i w2 P T F₂ p0 prest (type-#⇛-NUM→! P T tyn) nty (eqTypes-mon (uni i) tyt w2 (⊑-trans· e1 e2)) (equalInType-refl (equalInType-sym (equalInType-mon F∈ w2 (⊑-trans· e1 e2))))) a∈))
               (λ w2 e2 a₁ a₂ a∈ →
                 →≡equalInType
                   (sym (sub0-contDiag-EQ F₁ (#tab F₂ 0 #INIT) a₁ _))
                   (semCondEQ2
                     kb cn can exb gc i w2 P T F₁ F₂ a₁ (#APPLY #lamAX a₁) (#APPLY #lamAX a₂)
                     p0 nty tyn prest (eqTypes-mon (uni i) tyt w2 (⊑-trans· e1 e2))
                     (equalInType-mon F∈ w2 (⊑-trans· e1 e2))
                     (equalInType-refl a∈)))


-- TODO: get rid of the name by adding a FRESH
contDiagVal : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
              (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T : CTerm)
              → P 0
              → #⇛!-NUM-type P T
              → type-#⇛-NUM P T
              → type-preserves-#⇛ T
              → isType i w T
              → ∈Type i w (#contDiag T) #contDiagExt
contDiagVal kb cn can exb gc i w P T p0 nty tyn prest tyt =
  equalInType-PI
    {i} {w} {#FunBarP T}
    (λ w1 e1 → isType-FunBarP i w1 T (eqTypes-mon (uni i) tyt w1 e1))
    (λ w1 e1 F₁ F₂ eF →
      →≡equalTypes
        (sym (sub0-contDiag-subsing T F₁)) (sym (sub0-contDiag-subsing T F₂))
        (eqTypesSUBSING← (contDiagVal-type1 kb i w1 P T F₁ F₂ (eqTypes-mon (uni i) tyt w1 e1) (type-#⇛-NUM→! P T tyn) nty eF)))
    h1
  where
    h1 : ∀𝕎 w (λ w' _ → (F₁ F₂ : CTerm) → equalInType i w' (#FunBarP T) F₁ F₂
                      →  equalInType
                            i w' (sub0 F₁ (#[0]SUBSING (#[0]SUM (#[0]IndBar T) (#[1]PI (#[1]NAT→!T T) (#[2]EQ (#[2]APPLY #[2]VAR2 #[2]VAR0) (#[2]follow010) #[2]NAT)))))
                            (#APPLY #contDiagExt F₁) (#APPLY #contDiagExt F₂))
    h1 w1 e1 F₁ F₂ F∈ =
      →≡equalInType
        (sym (sub0-contDiag-subsing T F₁))
        (→equalInTypeSUBSING (contDiagVal-type1 kb i w1 P T F₁ F₁ (eqTypes-mon (uni i) tyt w1 e1) (type-#⇛-NUM→! P T tyn) nty (equalInType-refl F∈)) (Mod.∀𝕎-□ M h2))
      where
        h2 : ∀𝕎 w1 (λ w' _ →
                SUBSINGeq
                  (equalInType i w' (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY (CTerm→CTerm1 F₁) #[1]VAR0) follow1 #[1]NAT))))
                  (#APPLY #contDiagExt F₁)
                  (#APPLY #contDiagExt F₂))
        h2 w2 e2 = h3 , h4
          where
            h3 : ∈Type i w2 (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))) (#APPLY #contDiagExt F₁)
            h3 = contDiagVal1 kb cn can exb gc i w2 P T F₁ F₁ p0 nty tyn prest (eqTypes-mon (uni i) tyt w2 (⊑-trans· e1 e2)) (equalInType-refl (equalInType-mon F∈ w2 e2))

            h4 : ∈Type i w2 (#SUM (#IndBar T) (#[0]PI (#[0]NAT→!T T) (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))) (#APPLY #contDiagExt F₂)
            h4 = contDiagVal1 kb cn can exb gc i w2 P T F₁ F₂ p0 nty tyn prest (eqTypes-mon (uni i) tyt w2 (⊑-trans· e1 e2)) (equalInType-mon F∈ w2 e2)


Pℕ : ℕ → Set
Pℕ n = ⊤


Pℕ0 : Pℕ 0
Pℕ0 = tt


#⇛!-NUM-typeℕ : #⇛!-NUM-type Pℕ #NAT
#⇛!-NUM-typeℕ {i} {w} {n} pn = NUM-equalInType-NAT i w n


type-#⇛-NUMℕ : type-#⇛-NUM Pℕ #NAT
type-#⇛-NUMℕ {i} {w} {a} {b} a∈ =
  Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w a b a∈)
  where
    aw : ∀𝕎 w (λ w' e' → NATeq w' a b
                        → Σ ℕ (λ n → a #⇛ #NUM n at w' × b #⇛ #NUM n at w' × Pℕ n))
    aw w1 e1 (k , c₁ , c₂) = k , c₁ , c₂ , tt


type-preserves-#⇛ℕ : type-preserves-#⇛ #NAT
type-preserves-#⇛ℕ i w a₁ a₂ b₁ b₂ c₁ c₂ a∈ =
  →equalInType-NAT i w a₁ b₁ (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w a₂ b₂ a∈))
  where
    aw : ∀𝕎 w (λ w' e' → NATeq w' a₂ b₂ → NATeq w' a₁ b₁)
    aw w1 e1 (k , d₁ , d₂) = k ,
                             #⇛-trans {w1} {a₁} {a₂} {#NUM k} (∀𝕎-mon e1 c₁) d₁ ,
                             #⇛-trans {w1} {b₁} {b₂} {#NUM k} (∀𝕎-mon e1 c₂) d₂


contDiagVal-NAT : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
                  (i : ℕ) (w : 𝕎·)
                  → ∈Type i w (#contDiag #NAT) #contDiagExt
contDiagVal-NAT kb cn can exb gc i w =
  contDiagVal kb cn can exb gc i w Pℕ #NAT Pℕ0 #⇛!-NUM-typeℕ type-#⇛-NUMℕ type-preserves-#⇛ℕ eqTypesNAT

\end{code}
