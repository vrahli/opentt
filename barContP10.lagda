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
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalInType-trans)
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
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (isType-IndBarB ; equalTypes-IndBarC)
--open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (seq2list ; mseq∈baire)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (INIT)
--open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (#FunBarP ; FunBarP ; sem)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (follow ; #follow)
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


→equalInType-follow∈NAT : {i : ℕ} {w : 𝕎·} {W₁ W₂ a₁ a₂ : CTerm}
                            → equalInType i w #IndBar W₁ W₂
                            → equalInType i w #BAIRE! a₁ a₂
                            → equalInType i w #NAT (#follow a₁ W₁ 0) (#follow a₂ W₂ 0)
→equalInType-follow∈NAT {i} {w} {W₁} {W₂} {a₁} {a₂} W∈ a∈ =
  {!!}


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
        (eqTypesSUBSING←
          (eqTypesSUM←
            (λ w2 e2 → isType-IndBar i w2)
            (λ w2 e2 W₁ W₂ eqw →
              →≡equalTypes
                (sym (sub0-contDiag-PI F₁ W₁ _)) (sym (sub0-contDiag-PI F₂ W₂ _))
                (eqTypesPI←
                  (λ w3 e3 → isType-BAIRE!)
                  (λ w3 e3 a₁ a₂ eqa →
                    →≡equalTypes
                      (sym (sub0-contDiag-EQ F₁ W₁ a₁ _)) (sym (sub0-contDiag-EQ F₂ W₂ a₂ _))
                      (eqTypesEQ←
                        {_} {_} {#APPLY F₁ a₁} {#follow a₁ W₁ 0} {#APPLY F₂ a₂} {#follow a₂ W₂ 0} {#NAT} {#NAT}
                        eqTypesNAT
                        (APPLY-FunBarP-BAIRE!→ (equalInType-mon eF w3 (⊑-trans· e2 e3)) eqa)
                        {!!})))))))
    {!!}

\end{code}
