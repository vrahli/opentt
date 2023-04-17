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
open import compatible
open import progress
open import getChoice
open import newChoice
open import freeze
open import mod
open import choiceExt
open import choiceVal


-- An instance with Kripke bars (inKripkeBar-Bar) and references

module modInstanceKripkeRefBool (E0 : Extensionality 0ℓ 0ℓ) (E : Extensionality 0ℓ 3ℓ)
       where


open import encoding3(E0)

open import worldInstanceRef2(E0)

W : PossibleWorlds
W = PossibleWorldsRef

C : Choice
C = choiceRef

K : Compatible W C
K = compatibleREF

P : Progress W C K
P = progressREF

open import barKripke(W)

M : Mod W
M = inKripkeBar-Mod

G : GetChoice W C K
G = getChoiceRef

N : NewChoice W C K G
N = newChoiceRef

F : Freeze W C K P G N
F = freezeREF

X : ChoiceExt W C
X = choiceExtRef

V : ChoiceVal W C K G X N enc
V = choiceValRef

open import worldDef(W)
open import bar(W)
open import mod(W)
--open import barOpen(W)
open import choiceDef{1ℓ}(C)
open import compatibleDef(W)(C)(K)
open import progressDef(W)(C)(K)(P)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(enc)(V)
open import newChoiceDef(W)(C)(K)(G)(N)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

--open import barBeth(W)(C)(K)(P)
open import barI(W)(M)--(C)(K)(P)
open import computation(W)(C)(K)(G)(X)(N)(enc)

open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)



Typeℂ₀₁-kripke-ref : CTerm
Typeℂ₀₁-kripke-ref = #QTBOOL!


Typeℂ₀₁-isType-kripke-bar : (u : ℕ) (w : 𝕎·) → isType u w Typeℂ₀₁-kripke-ref
Typeℂ₀₁-isType-kripke-bar u w = eqTypesQTBOOL!


ℂ₀∈Typeℂ₀₁-kripke-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-kripke-ref Cℂ₀
ℂ₀∈Typeℂ₀₁-kripke-ref u w = INL-equalInType-QTBOOL! u w #AX #AX


ℂ₁∈Typeℂ₀₁-kripke-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-kripke-ref Cℂ₁
ℂ₁∈Typeℂ₀₁-kripke-ref u w = INR-equalInType-QTBOOL! u w #AX #AX


isvalue-choice : (c : ℂ·) → #isValue (ℂ→C· c)
isvalue-choice true = tt
isvalue-choice false = tt



#⇓-true : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓ ℂ→C· c at w
          → a #⇓ #INL x at w
          → c ≡ true
#⇓-true w a x true c₁ c₂ = refl
#⇓-true w a x false c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INL x ≡ #BFALSE
    z ()



#⇓-false : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓ ℂ→C· c at w
          → a #⇓ #INR x at w
          → c ≡ false
#⇓-false w a x false c₁ c₂ = refl
#⇓-false w a x true c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INR x ≡ #BTRUE
    z ()



#⇓!-true : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓! ℂ→C· c at w
          → a #⇓! #INL x at w
          → c ≡ true
#⇓!-true w a x true c₁ c₂ = refl
#⇓!-true w a x false c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓!-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INL x ≡ #BFALSE
    z ()



#⇓!-false : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓! ℂ→C· c at w
          → a #⇓! #INR x at w
          → c ≡ false
#⇓!-false w a x false c₁ c₂ = refl
#⇓!-false w a x true c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓!-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INR x ≡ #BTRUE
    z ()



∈Typeℂ₀₁→-kripke-ref : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                         → equalInType i w Typeℂ₀₁-kripke-ref a b → □· w (λ w' _ → #weakℂEq w' a b)
∈Typeℂ₀₁→-kripke-ref i w a b eqi = Mod.∀𝕎-□Func M aw (equalInType-QTBOOL!→ i w a b eqi)
  where
    aw : ∀𝕎 w (λ w' e' → #weakBool! w' a b → #weakℂEq w' a b)
    aw w1 e1 h w2 e2 = lift j
      where
        j : (c₁ c₂ : ℂ·) → ⌜ a ⌝ ⇓! ℂ→T c₁ at w2 → ⌜ b ⌝ ⇓! ℂ→T c₂ at w2 → ∼C! w2 (ℂ→C· c₁) (ℂ→C· c₂)
        j c₁ c₂ comp₁ comp₂ = c (snd (snd (lower (h w2 e2)))) --∼T-trans (∼T← comp₁) (∼T-trans (∼T-trans (∼T→ (fst (snd (lower (h w2 e2))))) (∼T← (snd (snd (lower (h w2 e2)))))) (∼T→ comp₂))
          where
            x : CTerm
            x = fst (lower (h w2 e2))

            y : CTerm
            y = fst (snd (lower (h w2 e2)))

            c : ((a #⇓! #INL x at w2 × b #⇓! #INL y at w2) ⊎ (a #⇓! #INR x at w2 × b #⇓! #INR y at w2))
                → ∼C! w2 (ℂ→C· c₁) (ℂ→C· c₂)
            c (inj₁ (c1 , c2)) rewrite #⇓!-true w2 a x c₁ comp₁ c1 | #⇓!-true w2 b y c₂ comp₂ c2 = ∼C!-refl {w2} {#BTRUE}
            c (inj₂ (c1 , c2)) rewrite #⇓!-false w2 a x c₁ comp₁ c1 | #⇓!-false w2 b y c₂ comp₂ c2 = ∼C!-refl {w2} {#BFALSE}



→∈Typeℂ₀₁-kripke-ref : (i : ℕ) {w : 𝕎·} {n : ℕ} {c : Name}
                      → □· w (λ w' _ → weakℂ₀₁M w' (getT n c))
                      → ∈Type i w Typeℂ₀₁-kripke-ref (#APPLY (#CS c) (#NUM n))
→∈Typeℂ₀₁-kripke-ref i {w} {n} {c} h =
  →equalInType-QTBOOL! i w (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
                     (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → weakℂ₀₁M w' (getT n c) → #weakBool! w' (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n)))
    aw w1 e1 z w2 e2 = lift (x (snd (snd (lower (z w2 e2)))))
      where
        t : Term
        t = fst (lower (z w2 e2))

        g : getT n c w2 ≡ just t
        g = fst (snd (lower (z w2 e2)))

        x : (t ⇓! Tℂ₀ at w2 ⊎ t ⇓! Tℂ₁ at w2)
            → #⇓!same-bool w2 (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
        x (inj₁ y) = #AX , #AX , inj₁ (⇓!-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 w2 n c refl g) y , ⇓!-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 w2 n c refl g) y)
        x (inj₂ y) = #AX , #AX , inj₂ (⇓!-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 w2 n c refl g) y , ⇓!-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 w2 n c refl g) y)



□·-choice-kripke-ref : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                        → compatible· c w r
                        → □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
□·-choice-kripke-ref w c m r (v , f , i , sat) =
  trivialK𝔹 w , j
  where
    j : ∈𝔹 {K𝔹bars} (trivialK𝔹 w) (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
    j {w1} e1 b w2 e2 z w3 e3 rewrite fst (snd (snd (⊑-pres-getRef (⊑-trans· z e3) i))) =
      lift (fst (⊑-pres-getRef (⊑-trans· z e3) i) ,
            refl ,
            getRefChoiceCompatible
              c r w3 m
              (fst (⊑-pres-getRef (⊑-trans· z e3) i))
              (⊑-compatibleRef (⊑-trans· z e3) (v , f , i , sat))
              gc)
      where
        gc : getRefChoice m c w3 ≡ just (fst (⊑-pres-getRef (⊑-trans· z e3) i))
        gc rewrite fst (snd (snd (⊑-pres-getRef (⊑-trans· z e3) i))) = refl



followChoice-kripke-ref : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                        → □· w f
                        → onlyℂ∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)
followChoice-kripke-ref c {w} {f} {r} (bar , i) ioc comp fb =
  w , ⊑-refl· _ , ioc , comp , fb ,
  i (⊑-refl· _) (K𝔹all bar) w (⊑-refl· _) (⊑-refl· _)



open import choiceBar(W)(M)(C)(K)(P)(G)(X)(N)(enc)(V)(F)(E)

kripkeRef-choiceBar : ChoiceBar
kripkeRef-choiceBar =
  mkChoiceBar
    Typeℂ₀₁-kripke-ref
    Typeℂ₀₁-isType-kripke-bar
    ℂ₀∈Typeℂ₀₁-kripke-ref
    ℂ₁∈Typeℂ₀₁-kripke-ref
    ∈Typeℂ₀₁→-kripke-ref
    →∈Typeℂ₀₁-kripke-ref
    equalTerms-pres-#⇛-left-QTBOOL!
    equalTerms-pres-#⇛-left-rev-QTBOOL!
    □·-choice-kripke-ref
    followChoice-kripke-ref

\end{code}
