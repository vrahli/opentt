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
open import compatible
open import progress
open import getChoice
open import newChoice
open import freeze
open import mod
open import choiceExt


-- An instance with beth bars (inBethBar-Bar) and references
-- As oppposed to modInstanceBethRef, which relies on choices of nats, this one relies on bools

module modInstanceBethRef2 (E : Extensionality 0ℓ 3ℓ)
       where


open import worldInstanceRef2

W : PossibleWorlds
W = PossibleWorldsRef

C : Choice
C = choiceRef

K : Compatible W C
K = compatibleREF

P : Progress W C K
P = progressREF

open import barBeth(W)(C)(K)(P)

M : Mod W
M = inBethBar-Mod

G : GetChoice W C K
G = getChoiceRef

N : NewChoice W C K G
N = newChoiceRef

F : Freeze W C K P G N
F = freezeREF

X : ChoiceExt W C K G
X = choiceExtRef

open import worldDef(W)
open import bar(W)
open import mod(W)
--open import barOpen(W)
open import choiceDef{1ℓ}(C)
open import compatibleDef(W)(C)(K)
open import progressDef(W)(C)(K)(P)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import newChoiceDef(W)(C)(K)(G)(N)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

--open import barBeth(W)(C)(K)(P)
open import barI(W)(M)(C)(K)(P)
open import computation(W)(C)(K)(G)

open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)



Typeℂ₀₁-beth-ref : CTerm
Typeℂ₀₁-beth-ref = #QTBOOL


Typeℂ₀₁-isType-beth-bar : (u : ℕ) (w : 𝕎·) → isType u w Typeℂ₀₁-beth-ref
Typeℂ₀₁-isType-beth-bar u w = eqTypesQTBOOL


ℂ₀∈Typeℂ₀₁-beth-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-ref Cℂ₀
ℂ₀∈Typeℂ₀₁-beth-ref u w = INL-equalInType-QTBOOL u w #AX #AX


ℂ₁∈Typeℂ₀₁-beth-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-ref Cℂ₁
ℂ₁∈Typeℂ₀₁-beth-ref u w = INR-equalInType-QTBOOL u w #AX #AX


isvalue-choice : (c : ℂ·) → #isValue (ℂ→C· c)
isvalue-choice true = tt
isvalue-choice false = tt


{--ℂ→C→∼ℂ-beth-ref : {w : 𝕎·} {c c1 c2 : ℂ·} → ℂ→C· c1 #⇓ ℂ→C· c2 at w → ∼C w c1 c → ∼C w c2 c
ℂ→C→∼ℂ-beth-ref {w} {c} {c1} {c2} comp sim
  rewrite sym (#NUMinj (#compVal comp (isvalue-choice c1))) -- (∼vals→isValue₁ sim)
  = sim--}


{--
isValueℂ₀-beth-ref : isValue Tℂ₀
isValueℂ₀-beth-ref = tt


isValueℂ₁-beth-ref : isValue Tℂ₁
isValueℂ₁-beth-ref = tt


ℂ₀≠ℂ₁-beth-ref : ¬ Cℂ₀ ≡ Cℂ₁
ℂ₀≠ℂ₁-beth-ref ()
--}


ℕ→B : ℕ → Bool
ℕ→B 0 = true
ℕ→B (suc _) = false



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



∈Typeℂ₀₁→-beth-ref : (i : ℕ) (w : 𝕎·) (a b : CTerm) → equalInType i w Typeℂ₀₁-beth-ref a b → □· w (λ w' _ → #weakℂEq w' a b)
∈Typeℂ₀₁→-beth-ref i w a b eqi = Mod.∀𝕎-□Func M aw (equalInType-QTBOOL→ i w a b eqi)
  where
    aw : ∀𝕎 w (λ w' e' → #weakBool w' a b → #weakℂEq w' a b)
    aw w1 e1 h w2 e2 = lift j
      where
        j : (c₁ c₂ : ℂ·) → ⌜ a ⌝ ⇓ ℂ→T c₁ at w2 → ⌜ b ⌝ ⇓ ℂ→T c₂ at w2 → ∼C w2 (ℂ→C· c₁) (ℂ→C· c₂)
        j c₁ c₂ comp₁ comp₂ = c (snd (snd (lower (h w2 e2)))) --∼T-trans (∼T← comp₁) (∼T-trans (∼T-trans (∼T→ (fst (snd (lower (h w2 e2))))) (∼T← (snd (snd (lower (h w2 e2)))))) (∼T→ comp₂))
          where
            x : CTerm
            x = fst (lower (h w2 e2))

            y : CTerm
            y = fst (snd (lower (h w2 e2)))

            c : ((a #⇓ #INL x at w2 × b #⇓ #INL y at w2) ⊎ (a #⇓ #INR x at w2 × b #⇓ #INR y at w2)) → ∼C w2 (ℂ→C· c₁) (ℂ→C· c₂)
            c (inj₁ (c1 , c2)) rewrite #⇓-true w2 a x c₁ comp₁ c1 | #⇓-true w2 b y c₂ comp₂ c2 = ∼C-refl {w2} {#BTRUE}
            c (inj₂ (c1 , c2)) rewrite #⇓-false w2 a x c₁ comp₁ c1 | #⇓-false w2 b y c₂ comp₂ c2 = ∼C-refl {w2} {#BFALSE}



→∈Typeℂ₀₁-beth-ref : (i : ℕ) {w : 𝕎·} {n : ℕ} {c : Name}
                      → □· w (λ w' _ → weakℂ₀₁M w' (getT n c))
                      → ∈Type i w Typeℂ₀₁-beth-ref (#APPLY (#CS c) (#NUM n))
→∈Typeℂ₀₁-beth-ref i {w} {n} {c} h =
  →equalInType-QTBOOL i w (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
                     (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → weakℂ₀₁M w' (getT n c) → #weakBool w' (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n)))
    aw w1 e1 z w2 e2 = lift (x (snd (snd (lower (z w2 e2)))))
      where
        t : Term
        t = fst (lower (z w2 e2))

        g : getT n c w2 ≡ just t
        g = fst (snd (lower (z w2 e2)))

        x : (t ⇓ Tℂ₀ at w2 ⊎ t ⇓ Tℂ₁ at w2)
            → #⇓same-bool w2 (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
        x (inj₁ y) = #AX , #AX , inj₁ (⇓-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 n c refl g) y , ⇓-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 n c refl g) y)
        x (inj₂ y) = #AX , #AX , inj₂ (⇓-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 n c refl g) y , ⇓-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 n c refl g) y)



□·-choice-beth-ref : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                        → compatible· c w r
                        → □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
□·-choice-beth-ref w c m r (v , f , i , sat) = trivialIS𝔹 w , j
  where
    j : inIS𝔹 (trivialIS𝔹 w) (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
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



followChoice-beth-ref : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                        → □· w f
                        → onlyℂ∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)
followChoice-beth-ref c {w} {f} {r} (bar , i) ioc comp fb =
  w , ⊑-refl· _ , ioc , comp , fb ,
  i e (BarredChain.b bp) (chain.seq (pchain.c pc) (BarredChain.n bp)) (BarredChain.ext bp) (⊑-refl· _)
  where
    pc : pchain w
    pc = 𝕎→pchain w

    bp : BarredChain (𝔹.bar bar) (pchain.c pc)
    bp = 𝔹.bars bar pc

    w' : 𝕎·
    w' = BarredChain.w' bp

    e : w ⊑· w'
    e = 𝔹.ext bar (BarredChain.b bp)



open import choiceBar(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)

bethRef-choiceBar : ChoiceBar
bethRef-choiceBar =
  mkChoiceBar
    Typeℂ₀₁-beth-ref
    Typeℂ₀₁-isType-beth-bar
    ℂ₀∈Typeℂ₀₁-beth-ref
    ℂ₁∈Typeℂ₀₁-beth-ref
    ∈Typeℂ₀₁→-beth-ref
    →∈Typeℂ₀₁-beth-ref
    □·-choice-beth-ref
    followChoice-beth-ref

\end{code}