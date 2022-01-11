\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred ; _⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Maybe
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties


open import util
open import calculus


module choiceBarInstanceRef where


open import worldInstanceRef
open import choiceDef{1ℓ}(choiceRef)
open import worldDef(PossibleWorldsRef)
open import getChoiceDef(PossibleWorldsRef)(choiceRef)(getChoiceRef)
open import newChoiceDef(PossibleWorldsRef)(choiceRef)(getChoiceRef)(newChoiceRef)
open import freezeDef(PossibleWorldsRef)(choiceRef)(getChoiceRef)(newChoiceRef)(freezeREF)
open import progressDef(PossibleWorldsRef)(choiceRef)(getChoiceRef)(newChoiceRef)(freezeREF)(progressREF)

open import bar(PossibleWorldsRef)(choiceRef)(getChoiceRef)(newChoiceRef)(freezeREF)(progressREF)
open import computation(PossibleWorldsRef)(choiceRef)(getChoiceRef)



-- We can use the trivial bar here because there are always choices available
choice-weakℕ-beth-ref : {w : 𝕎·} {c : Name} (m : ℕ) → compatible· c w Resℕ → inBethBar w (λ w' _ → weakℕM w' (getChoice· m c))
choice-weakℕ-beth-ref {w} {c} m (v , f , i , sat) = trivialIS𝔹 w , j
  where
    j : inIS𝔹 (trivialIS𝔹 w) (λ w' _ → weakℕM w' (getChoice· m c))
    j {w1} e1 b w2 e2 z w3 e3 = lift (fst h , gc , compn)
      where
        h : Σ Term (λ v' → Σ Bool (λ f' → getRef c w3 ≡ just (cell c Resℕ v' f') × pres-resSatRef v v' Resℕ × satFrozen v v' f f'))
        h = ⊑-pres-getRef (⊑-trans· z e3) i

        isn : Σ ℕ (λ m → fst h ≡ NUM m)
        isn = fst (snd (snd (snd h))) sat 0

        gc : getChoice· m c w3 ≡ just (fst h)
        gc rewrite fst (snd (snd h)) = refl

        compn : Σ ℕ (λ n → fst h ⇓ NUM n at w3)
        compn rewrite snd isn = fst isn , ⇓-refl (NUM (fst isn)) w3


{--
⊑-isOnlyChoice∈𝕎 : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} {u : Term}
                    → w1 ⊑· w2
                    → isOnlyChoice∈𝕎 u c w2
                    → isOnlyChoice∈𝕎 u c w1
⊑-isOnlyChoice∈𝕎 {c} {w1} {w2} {r} {u} e iso k t z with getRef⊎ c w1
... | inj₁ (cell n' r' v' f' , p) rewrite p  = {!!}
{-- | fst (snd (≽-pres-getCs e (getCs→≡Name-getCs {w1} p))) =
  iso k t (select++-just {0ℓ} {Term} {k} {l} {fst (≽-pres-getCs e (getCs→≡Name-getCs {w1} p))} z)--}
... | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym z))
--}

followChoice-beth-ref : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                        → inBethBar w f
                        → isOnlyChoice∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → Σ 𝕎· (λ w1 → Σ (w ⊑· w1) (λ e1 → isOnlyChoice∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
followChoice-beth-ref c {w} {f} {r} (bar , i) ioc comp fb =
  w , ⊑-refl· _ , ioc , comp , fb ,
  i e (BarsProp.b bp) (chain.seq (pchain.c pc) (BarsProp.n bp)) (BarsProp.ext bp) (⊑-refl· _)
  where
    pc : pchain w
    pc = 𝕎→pchain w

    bp : BarsProp (IS𝔹.bar bar) (pchain.c pc)
    bp = IS𝔹.bars bar pc

    w' : 𝕎·
    w' = BarsProp.w' bp

    e : w ⊑· w'
    e = IS𝔹.ext bar (BarsProp.b bp)

\end{code}
