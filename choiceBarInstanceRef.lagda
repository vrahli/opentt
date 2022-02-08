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


module choiceBarInstanceRef (E : Extensionality 0ℓ 3ℓ)
       where


open import worldInstanceRef
open import choiceDef{1ℓ}(choiceRef)
open import worldDef(PossibleWorldsRef)
open import compatibleDef(PossibleWorldsRef)(choiceRef)(compatibleREF)
open import progressDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)
open import getChoiceDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)
open import choiceExtDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(choiceExtRef)
open import newChoiceDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(newChoiceRef)
open import freezeDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(newChoiceRef)(freezeREF)

open import bar(PossibleWorldsRef)
open import barOpen(PossibleWorldsRef)
open import barBeth(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)
open import barI(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)
open import computation(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)

open import forcing(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(E)
open import props1(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(E)
open import props2(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(E)
open import props3(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(E)



Typeℂ₀₁-beth-ref : CTerm
Typeℂ₀₁-beth-ref = #QTNAT


Typeℂ₀₁-isType-beth-bar : (u : ℕ) (w : 𝕎·) → isType u w Typeℂ₀₁-beth-ref
Typeℂ₀₁-isType-beth-bar u w = eqTypesQTNAT


ℂ₀∈Typeℂ₀₁-beth-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-ref Cℂ₀
ℂ₀∈Typeℂ₀₁-beth-ref u w = NUM-equalInType-QTNAT u w 0


ℂ₁∈Typeℂ₀₁-beth-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-ref Cℂ₁
ℂ₁∈Typeℂ₀₁-beth-ref u w = NUM-equalInType-QTNAT u w 1


isvalue-choice : (c : ℂ·) → #isValue (ℂ→C· c)
isvalue-choice c = tt


ℂ→C→∼ℂ-beth-ref : {w : 𝕎·} {c c1 c2 : ℂ·} → ℂ→C· c1 #⇓ ℂ→C· c2 at w → ∼ℂ· c1 c → ∼ℂ· c2 c
ℂ→C→∼ℂ-beth-ref {w} {c} {c1} {c2} comp sim
  rewrite sym (ℂ→C-inj· {c1} {c2} (#compVal comp (isvalue-choice c1))) -- (∼vals→isValue₁ sim)
  = sim


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


∈Typeℂ₀₁→-beth-ref : (i : ℕ) (w : 𝕎·) (a b : CTerm) → equalInType i w Typeℂ₀₁-beth-ref a b → inbar w (λ w' _ → #weakℂEq w' a b)
∈Typeℂ₀₁→-beth-ref i w a b eqi = Bar.∀𝕎-inBarFunc barI aw (equalInType-QTNAT→ i w a b eqi)
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq w' a b → #weakℂEq w' a b)
    aw w1 e1 h w2 e2 = lift (fst (lower (h w2 e2)) ,
                             fst (lower (h w2 e2)) ,
                             fst (snd (lower (h w2 e2))) ,
                             snd (snd (lower (h w2 e2))) ,
                             refl) --∼vals-NUM)


→∈Typeℂ₀₁-beth-ref : (i : ℕ) {w : 𝕎·} {n : ℕ} {c : Name}
                      → inbar w (λ w' _ → weakℂ₀₁M w' (getT n c))
                      → ∈Type i w Typeℂ₀₁-beth-ref (#APPLY (#CS c) (#NUM n))
→∈Typeℂ₀₁-beth-ref i {w} {n} {c} h =
  →equalInType-QTNAT i w (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
                     (Bar.∀𝕎-inBarFunc barI aw h)
  where
    aw : ∀𝕎 w (λ w' e' → weakℂ₀₁M w' (getT n c) → #weakMonEq w' (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n)))
    aw w1 e1 z w2 e2 = lift (x (snd (snd (lower (z w2 e2)))))
      where
        t : Term
        t = fst (lower (z w2 e2))

        g : getT n c w2 ≡ just t
        g = fst (snd (lower (z w2 e2)))

        x : (t ⇓ Tℂ₀ at w2 ⊎ t ⇓ Tℂ₁ at w2)
            → Σ ℕ (λ n₁ → APPLY (CS c) (NUM n) ⇓ NUM n₁ at w2 × APPLY (CS c) (NUM n) ⇓ NUM n₁ at w2)
        x (inj₁ y) = 0 , ⇓-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 n c refl g) y , ⇓-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 n c refl g) y
        x (inj₂ y) = 1 , ⇓-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 n c refl g) y , ⇓-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 n c refl g) y


inbar-choice-beth-ref : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                        → compatible· c w r
                        → inBethBar w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
inbar-choice-beth-ref w c m r (v , f , i , sat) = trivialIS𝔹 w , j
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
                        → inBethBar w f
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


-- TODO: if we didn't want to rely on the choice instance at all,
-- we could add to getFreeze that we have ¬ freezable c w' in the extensions
¬followChoice-open-ref-aux : (w : 𝕎·)
                             → ¬((c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                                    → inOpenBar w f
                                    → onlyℂ∈𝕎 (Res.def r) c w
                                    → compatible· c w r
                                    → freezable· c w
                                    → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
¬followChoice-open-ref-aux w0 h =
  lower (snd (snd (snd (snd (snd q))))) (fst (snd (snd (snd (snd q)))))
  where
    r : Res{0ℓ}
    r = Resℂ₀₁

    c : Name
    c = newChoice· w0

    w : 𝕎·
    w = startNewChoice r w0

    f : wPred w
    f w' e = Lift 2ℓ (¬ freezable· c w')

    comp : compatible· c w r
    comp = startChoiceCompatible· r w0

    k : ℂ·
    k = ℂ₁·

    i : inOpenBar w f
    i w1 e1 = w2 , e2 , aw
      where
        w2 : 𝕎·
        w2 = freeze· c w1 k

        e2 : w1 ⊑· w2
        e2 = freeze⊑· c w1 k (⊑-compatible· e1 comp) λ n → inj₂ refl

        -- This we where we could modify getFreeze or add an axiom like freeze→¬freezable
        aw : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
        aw w3 e3 z = freeze→¬freezable {c} {w1} k (⊑-compatible· e1 comp) w3 e3

    oc : onlyℂ∈𝕎 (Res.def r) c w
    oc n = getChoice-startNewChoice· n r w0

    fb : freezable· c w
    fb = freezableStart· r w0

    q :  ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)
    q = h c {w} {f} {r} i oc comp fb


{--
-- We need 𝕎 to be non-empty
¬followChoice-open-ref : ¬((c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                           → inOpenBar w f
                           → isOnlyChoice∈𝕎 (Res.def r) c w
                           → compatible· c w r
                           → freezable· c w
                           → ∃𝕎 w (λ w1 e1 → isOnlyChoice∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
¬followChoice-open-ref h = {!!}
--}

\end{code}
