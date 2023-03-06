\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --experimental-lossy-unification #-}
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


module barContP10 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                  (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                  (X : ChoiceExt W C)
                  (N : NewChoice {L} W C K G)
                  (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                  (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N) using (≡APPLY ; ≡SUBSING ; ≡EQ ; upd)
--open import terms4(W)(C)(K)(G)(X)(N)
--open import terms5(W)(C)(K)(G)(X)(N)
--open import terms6(W)(C)(K)(G)(X)(N)
--open import terms7(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N) using (#APPLY2 ; #⇛-trans ; #INL¬≡INR)
open import terms9(W)(C)(K)(G)(X)(N) using (#BAIRE! ; BAIRE!)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#⇛-refl)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalInType-trans ; →equalInTypeSUBSING)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E) using (→equalInType-NAT! ; equalInType-W→)
--open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

--open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

--open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#upd ; #force ; equalInType-force)
--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#⇓sameℕ)
--open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (steps-sat-isHighestℕ ; ¬Names→updCtxt)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalInType-upd-force)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalInType-TPURE→ₗ ; equalInType-TPURE→ ; equalTypesTPURE ; isType-BAIRE→NAT)
--open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (isHighestℕ≤)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (isType-IndBarB ; equalTypes-IndBarC ; #INIT)
--open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (seq2list ; mseq∈baire)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (INIT)
--open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (#FunBarP ; FunBarP ; sem)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (follow ; #follow ; weq→follow-NATeq ; #tab)
--open import barContP8(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (follow-NUM-ETA)
open import barContP9(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (semCond)


contDiag : Term
contDiag =
  PI FunBarP
     (SUBSING
       (SUM IndBar (PI BAIRE! (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT))))


#contDiag : CTerm
#contDiag = ct contDiag c
  where
    c : # contDiag
    c = refl


contDiagExt : Name → Term
contDiagExt r =
  LAMBDA (PAIR (APPLY2 (loop r (VAR 0)) (NUM 0) INIT) lamAX)


#contDiagExt : Name → CTerm
#contDiagExt r = ct (contDiagExt r) c
  where
    c : # (contDiagExt r)
    c = refl


#contDiagExt⇛ : (r : Name) (F : CTerm) (w : 𝕎·)
                 → #APPLY (#contDiagExt r) F #⇛ #PAIR (#tab r F 0 #INIT) #lamAX at w
#contDiagExt⇛ r F w w1 e1 =
  lift (#⇓from-to→#⇓ {w1} {w1} {#APPLY (#contDiagExt r) F} {#PAIR (#tab r F 0 #INIT) #lamAX} (1 , ≡pair c refl))
  where
    c : sub ⌜ F ⌝ (PAIR (APPLY2 (loop r (VAR 0)) (NUM 0) INIT) lamAX)
        ≡ ⌜ #PAIR (#tab r F 0 #INIT) #lamAX ⌝
    c rewrite #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftUp 0 F
            | #shiftDown 4 F = refl


isType-FunBarP : (i : ℕ) (w : 𝕎·) → isType i w #FunBarP
isType-FunBarP i w = equalTypesTPURE (isType-BAIRE→NAT i w)


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


sub0-contDiag-subsing : (F : CTerm)
                        → sub0 F (ct0 (SUBSING (SUM IndBar (PI BAIRE! (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)))) refl)
                           ≡ #SUBSING (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F ⌟ #[1]VAR0) follow1 #[1]NAT)))
sub0-contDiag-subsing F = CTerm≡ e
  where
    e : ⌜ sub0 F (ct0 (SUBSING (SUM IndBar (PI BAIRE! (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)))) refl) ⌝
        ≡ ⌜ #SUBSING (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F ⌟ #[1]VAR0) follow1 #[1]NAT))) ⌝
    e rewrite #shiftUp 0 F | #shiftUp 0 F | #shiftUp 0 F | #shiftDown 2 F = refl


sub0-contDiag-PI : (F W : CTerm) (c : #[ [ 0 ] ] (PI BAIRE! (EQ (APPLY ⌜ F ⌝ (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)))
                   → sub0 W (ct0 (PI BAIRE! (EQ (APPLY ⌜ F ⌝ (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)) c)
                      ≡ #PI #BAIRE! (#[0]EQ (#[0]APPLY ⌞ F ⌟ #[0]VAR) (follow0 W) #[0]NAT)
sub0-contDiag-PI F W c = CTerm≡ e
  where
    e : ⌜ sub0 W (ct0 (PI BAIRE! (EQ (APPLY ⌜ F ⌝ (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)) c) ⌝
        ≡ ⌜ #PI #BAIRE! (#[0]EQ (#[0]APPLY ⌞ F ⌟ #[0]VAR) (follow0 W) #[0]NAT) ⌝
    e rewrite #shiftUp 0 W | #shiftUp 0 W
            | #subv 1 ⌜ W ⌝ ⌜ F ⌝ (CTerm.closed F)
            | #shiftDown 1 W | #shiftDown 1 F = refl


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


→≡equalTypes : {i : ℕ} {w : 𝕎·} {a1 a2 b1 b2 : CTerm}
                → a1 ≡ a2
                → b1 ≡ b2
                → equalTypes i w a1 b1
                → equalTypes i w a2 b2
→≡equalTypes {i} {w} {a1} {a2} {b1} {b2} e1 e2 h rewrite e1 | e2 = h


→≡equalInType : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                → T ≡ U
                → equalInType i w T a b
                → equalInType i w U a b
→≡equalInType {i} {w} {T} {U} {a} {b} e h rewrite e = h


isType-IndBar : (i : ℕ) (w : 𝕎·) → isType i w #IndBar
isType-IndBar i w =
  eqTypesW←
    {w} {i} {#IndBarB} {#IndBarC} {#IndBarB} {#IndBarC}
    (λ w1 e1 → isType-IndBarB i w1)
    (λ w1 e1 a b eqa → equalTypes-IndBarC  i w1 a b eqa)


isType-BAIRE! : {w : 𝕎·} {i : ℕ} → isType i w #BAIRE!
isType-BAIRE! {w} {i} = eqTypesFUN← {w} {i} {#NAT} {#NAT!} eqTypesNAT isTypeNAT!


APPLY-∈BAIRE!→NAT! : (i : ℕ) (w : 𝕎·) (f₁ f₂ a₁ a₂ : CTerm)
                       → equalInType i w #BAIRE! f₁ f₂
                       → equalInType i w #NAT a₁ a₂
                       → equalInType i w #NAT! (#APPLY f₁ a₁) (#APPLY f₂ a₂)
APPLY-∈BAIRE!→NAT! i w f₁ f₂ a₁ a₂ f∈ a∈ =
  equalInType-FUN→ f∈ w (⊑-refl· w) a₁ a₂ a∈


NAT!→NAT : (i : ℕ) (w : 𝕎·) (a b : CTerm)
            → equalInType i w #NAT! a b
            → equalInType i w #NAT a b
NAT!→NAT i w a b h = →equalInType-NAT i w a b (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w a b h))
  where
    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b → NATeq w' a b)
    aw w1 e1 (k , c1 , c2) = k , #⇛!→#⇛ {w1} {a} {#NUM k} c1 , #⇛!→#⇛ {w1} {b} {#NUM k} c2


BAIRE!→BAIRE : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                → equalInType i w #BAIRE! a b
                → equalInType i w #BAIRE a b
BAIRE!→BAIRE i w a b h =
  equalInType-FUN eqTypesNAT eqTypesNAT aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂ → equalInType i w' #NAT (#APPLY a a₁) (#APPLY b a₂))
    aw w1 e1 a₁ a₂ ea = NAT!→NAT i w1 (#APPLY a a₁) (#APPLY b a₂) (equalInType-FUN→ h w1 e1 a₁ a₂ ea)



APPLY-FunBarP-BAIRE!→ : {i : ℕ} {w : 𝕎·} {F₁ F₂ a₁ a₂ : CTerm}
                         → equalInType i w #FunBarP F₁ F₂
                         → equalInType i w #BAIRE! a₁ a₂
                         → equalInType i w #NAT (#APPLY F₁ a₁) (#APPLY F₂ a₂)
APPLY-FunBarP-BAIRE!→ {i} {w} {F₁} {F₂} {a₁} {a₂} F∈P a∈ =
  equalInType-FUN→ F∈ w (⊑-refl· w) a₁ a₂ (BAIRE!→BAIRE i w a₁ a₂ a∈)
  where
    F∈ : equalInType i w #FunBar F₁ F₂
    F∈ = equalInType-TPURE→ F∈P


→equalInType-follow∈NAT : (kb : K□) {i : ℕ} {w : 𝕎·} {W₁ W₂ a₁ a₂ : CTerm}
                            → equalInType i w #IndBar W₁ W₂
                            → equalInType i w #BAIRE! a₁ a₂
                            → equalInType i w #NAT (#follow a₁ W₁ 0) (#follow a₂ W₂ 0)
→equalInType-follow∈NAT kb {i} {w} {W₁} {W₂} {a₁} {a₂} W∈ a∈ =
  →equalInType-NAT
    i w (#follow a₁ W₁ 0) (#follow a₂ W₂ 0)
    (Mod.∀𝕎-□Func M aw (equalInType-W→ i w #IndBarB #IndBarC W₁ W₂ W∈))
  where
    aw : ∀𝕎 w (λ w' e' → weq (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC)) w' W₁ W₂
                        → NATeq w' (#follow a₁ W₁ 0) (#follow a₂ W₂ 0))
    aw w1 e1 h =
      weq→follow-NATeq
        kb i w1 W₁ W₂ a₁ a₂ 0 h
        (λ k → equalInType-FUN→ a∈ w1 e1 (#NUM k) (#NUM k) (NUM-equalInType-NAT i w1 k))


contDiagVal-type3 : (kb : K□) (i : ℕ) (w : 𝕎·) (F₁ F₂ W₁ W₂ a₁ a₂ : CTerm)
                    → equalInType i w #FunBarP F₁ F₂
                    → equalInType i w #IndBar W₁ W₂
                    → equalInType i w #BAIRE! a₁ a₂
                    → equalTypes
                         i w
                         (#EQ (#APPLY F₁ a₁) (#follow a₁ W₁ 0) #NAT)
                         (#EQ (#APPLY F₂ a₂) (#follow a₂ W₂ 0) #NAT)
contDiagVal-type3 kb i w F₁ F₂ W₁ W₂ a₁ a₂ F∈ W∈ a∈ =
  eqTypesEQ←
    {_} {_} {#APPLY F₁ a₁} {#follow a₁ W₁ 0} {#APPLY F₂ a₂} {#follow a₂ W₂ 0} {#NAT} {#NAT}
    eqTypesNAT
    (APPLY-FunBarP-BAIRE!→ F∈ a∈)
    (→equalInType-follow∈NAT kb {i} {w} {W₁} {W₂} {a₁} {a₂} W∈ a∈)


contDiagVal-type2 : (kb : K□) (i : ℕ) (w : 𝕎·) (F₁ F₂ W₁ W₂ : CTerm)
                    → equalInType i w #FunBarP F₁ F₂
                    → equalInType i w #IndBar W₁ W₂
                    → equalTypes
                         i w
                         (#PI #BAIRE! (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) (follow0 W₁) #[0]NAT))
                         (#PI #BAIRE! (#[0]EQ (#[0]APPLY ⌞ F₂ ⌟ #[0]VAR) (follow0 W₂) #[0]NAT))
contDiagVal-type2 kb i w F₁ F₂ W₁ W₂ F∈ W∈ =
  eqTypesPI←
    (λ w1 e1 → isType-BAIRE!)
    (λ w1 e1 a₁ a₂ a∈ →
      →≡equalTypes
        (sym (sub0-contDiag-EQ F₁ W₁ a₁ _)) (sym (sub0-contDiag-EQ F₂ W₂ a₂ _))
        (contDiagVal-type3 kb i w1 F₁ F₂ W₁ W₂ a₁ a₂ (equalInType-mon F∈ w1 e1) (equalInType-mon W∈ w1 e1) a∈))


contDiagVal-type1 : (kb : K□) (i : ℕ) (w : 𝕎·) (F₁ F₂ : CTerm)
                    → equalInType i w #FunBarP F₁ F₂
                    → equalTypes
                         i w
                         (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT)))
                         (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F₂ ⌟ #[1]VAR0) follow1 #[1]NAT)))
contDiagVal-type1 kb i w F₁ F₂ F∈ =
  eqTypesSUM←
    (λ w1 e1 → isType-IndBar i w1)
    (λ w1 e1 W₁ W₂ W∈ →
      →≡equalTypes
        (sym (sub0-contDiag-PI F₁ W₁ _)) (sym (sub0-contDiag-PI F₂ W₂ _))
        (contDiagVal-type2 kb i w1 F₁ F₂ W₁ W₂ (equalInType-mon F∈ w1 e1) W∈))


semCondEQ : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (F f : CTerm) (a b : CTerm)
            → compatible· r w Res⊤
            → ∈Type i w #FunBarP F
            → ∈Type i w #BAIRE! f
            → equalInType i w (#EQ (#APPLY F f) (#follow f (#tab r F 0 #INIT) 0) #NAT) a b
semCondEQ kb cn can exb gc i w r F f a b compat F∈P f∈ =
  equalInType-EQ
    eqTypesNAT
    (Mod.∀𝕎-□ M (λ w1 e1 → semCond kb cn can exb gc i w1 r F f (⊑-compatible· e1 compat) (equalInType-mon F∈P w1 e1) (equalInType-mon f∈ w1 e1)))


semCond2 : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
          (i : ℕ) (w : 𝕎·) (r : Name) (F₁ F₂ f : CTerm)
          → compatible· r w Res⊤
          → equalInType i w #FunBarP F₁ F₂
          → ∈Type i w #BAIRE! f
          → equalInType i w #NAT (#APPLY F₁ f) (#follow f (#tab r F₂ 0 #INIT) 0)
semCond2 kb cn can exb gc i w r F₁ F₂ f compat F∈P f∈ =
  equalInType-trans eqn (semCond kb cn can exb gc i w r F₂ f compat (equalInType-refl (equalInType-sym F∈P)) f∈)
  where
    eqn : equalInType i w #NAT (#APPLY F₁ f) (#APPLY F₂ f)
    eqn = APPLY-FunBarP-BAIRE!→ F∈P f∈


semCondEQ2 : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (F₁ F₂ f : CTerm) (a b : CTerm)
            → compatible· r w Res⊤
            → equalInType i w #FunBarP F₁ F₂
            → ∈Type i w #BAIRE! f
            → equalInType i w (#EQ (#APPLY F₁ f) (#follow f (#tab r F₂ 0 #INIT) 0) #NAT) a b
semCondEQ2 kb cn can exb gc i w r F₁ F₂ f a b compat F∈P f∈ =
  equalInType-EQ
    eqTypesNAT
    (Mod.∀𝕎-□ M (λ w1 e1 → semCond2 kb cn can exb gc i w1 r F₁ F₂ f (⊑-compatible· e1 compat) (equalInType-mon F∈P w1 e1) (equalInType-mon f∈ w1 e1)))


contDiagVal1 : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
               (i : ℕ) (w : 𝕎·) (F₁ F₂ : CTerm) (r : Name)
               → compatible· r w Res⊤
               → equalInType i w #FunBarP F₁ F₂
               → ∈Type i w (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))) (#APPLY (#contDiagExt r) F₂)
contDiagVal1 kb cn can exb gc i w F₁ F₂ r compat F∈ =
  equalInType-SUM
    (λ w1 e1 → isType-IndBar i w1)
    (λ w1 e1 W₁ W₂ W∈ →
      →≡equalTypes
        (sym (sub0-contDiag-PI F₁ W₁ _)) (sym (sub0-contDiag-PI F₁ W₂ _))
        (contDiagVal-type2 kb i w1 F₁ F₁ W₁ W₂ (equalInType-refl (equalInType-mon F∈ w1 e1)) W∈))
    (Mod.∀𝕎-□ M h1)
  where
    h1 : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #IndBar)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))))
                                w' (#APPLY (#contDiagExt r) F₂) (#APPLY (#contDiagExt r) F₂))
    h1 w1 e1 =
      #tab r F₂ 0 #INIT , #tab r F₂ 0 #INIT , #lamAX , #lamAX ,
      sem kb cn can exb gc i w1 r F₂ (⊑-compatible· e1 compat) (equalInType-refl (equalInType-sym (equalInType-mon F∈ w1 e1))) ,
      #contDiagExt⇛ r F₂ w1 ,
      #contDiagExt⇛ r F₂ w1 ,
      →≡equalInType (sym (sub0-contDiag-PI F₁ (#tab r F₂ 0 #INIT) _)) h2
      where
        h2 : equalInType i w1 (#PI #BAIRE! (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) (follow0 (#tab r F₂ 0 #INIT)) #[0]NAT)) #lamAX #lamAX
        h2 = equalInType-PI
               (λ w2 e2 → isType-BAIRE!)
               (λ w2 e2 a₁ a₂ a∈ →
                 →≡equalTypes
                   (sym (sub0-contDiag-EQ F₁ (#tab r F₂ 0 #INIT) a₁ _)) (sym (sub0-contDiag-EQ F₁ (#tab r F₂ 0 #INIT) a₂ _))
                   (contDiagVal-type3
                     kb i w2 F₁ F₁ (#tab r F₂ 0 #INIT) (#tab r F₂ 0 #INIT) a₁ a₂
                     (equalInType-refl (equalInType-mon F∈ w2 (⊑-trans· e1 e2)))
                     (sem kb cn can exb gc i w2 r F₂ (⊑-compatible· (⊑-trans· e1 e2) compat) (equalInType-refl (equalInType-sym (equalInType-mon F∈ w2 (⊑-trans· e1 e2))))) a∈))
               (λ w2 e2 a₁ a₂ a∈ →
                 →≡equalInType
                   (sym (sub0-contDiag-EQ F₁ (#tab r F₂ 0 #INIT) a₁ _))
                   (semCondEQ2
                     kb cn can exb gc i w2 r F₁ F₂ a₁ (#APPLY #lamAX a₁) (#APPLY #lamAX a₂)
                     (⊑-compatible· (⊑-trans· e1 e2) compat)
                     ((equalInType-mon F∈ w2 (⊑-trans· e1 e2)))
                     (equalInType-refl a∈)))


-- TODO: get rid of the name by adding a FRESH
contDiagVal : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
              (i : ℕ) (w : 𝕎·) (r : Name)
              → compatible· r w Res⊤
              → ∈Type i w #contDiag (#contDiagExt r)
contDiagVal kb cn can exb gc i w r compat =
  equalInType-PI
    {i} {w} {#FunBarP}
    {ct0 (SUBSING (SUM IndBar (PI BAIRE! (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)))) refl}
    (λ w1 e1 → isType-FunBarP i w1)
    (λ w1 e1 F₁ F₂ eF →
      →≡equalTypes
        (sym (sub0-contDiag-subsing F₁)) (sym (sub0-contDiag-subsing F₂))
        (eqTypesSUBSING← (contDiagVal-type1 kb i w1 F₁ F₂ eF)))
    h1
  where
    h1 : ∀𝕎 w (λ w' _ → (F₁ F₂ : CTerm) → equalInType i w' #FunBarP F₁ F₂
                      →  equalInType
                            i w' (sub0 F₁ (ct0 (SUBSING (SUM IndBar (PI BAIRE! (EQ (APPLY (VAR 2) (VAR 0)) (follow (VAR 0) (VAR 1) 0) NAT)))) refl))
                            (#APPLY (#contDiagExt r) F₁) (#APPLY (#contDiagExt r) F₂))
    h1 w1 e1 F₁ F₂ F∈ =
      →≡equalInType
        (sym (sub0-contDiag-subsing F₁))
        (→equalInTypeSUBSING (contDiagVal-type1 kb i w1 F₁ F₁ (equalInType-refl F∈)) (Mod.∀𝕎-□ M h2))
      where
        h2 : ∀𝕎 w1 (λ w' _ →
                SUBSINGeq
                  (equalInType i w' (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY (CTerm→CTerm1 F₁) #[1]VAR0) follow1 #[1]NAT))))
                  (#APPLY (#contDiagExt r) F₁)
                  (#APPLY (#contDiagExt r) F₂))
        h2 w2 e2 = h3 , h4
          where
            h3 : ∈Type i w2 (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))) (#APPLY (#contDiagExt r) F₁)
            h3 = contDiagVal1 kb cn can exb gc i w2 F₁ F₁ r (⊑-compatible· (⊑-trans· e1 e2) compat) (equalInType-refl (equalInType-mon F∈ w2 e2))

            h4 : ∈Type i w2 (#SUM #IndBar (#[0]PI #[0]BAIRE! (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) follow1 #[1]NAT))) (#APPLY (#contDiagExt r) F₂)
            h4 = contDiagVal1 kb cn can exb gc i w2 F₁ F₂ r (⊑-compatible· (⊑-trans· e1 e2) compat) (equalInType-mon F∈ w2 e2)

\end{code}
