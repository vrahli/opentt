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
open import world
open import choice


module choiceBarInstanceRef where


open import worldInstanceRef
open import worldDef(PossibleWorldsRef)
open import choice(PossibleWorldsRef)
open import choiceDef(PossibleWorldsRef)(refChoice)
open import bar(PossibleWorldsRef)(refChoice)
open import computation(PossibleWorldsRef)(refChoice)



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


followChoice-beth-ref : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                        → inBethBar w f
                        → isOnlyChoice∈𝕎 (Res.def r) c w
                        → compatible· c w r
                        → freezable· c w
                        → Σ 𝕎· (λ w1 → Σ (w ⊑· w1) (λ e1 → isOnlyChoice∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
followChoice-beth-ref c {w} {f} {r} i ioc comp fb = {!!}
\end{code}
