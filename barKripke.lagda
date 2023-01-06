\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; _⊔_) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; pred)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Empty


open import util
open import calculus
open import world
open import choice
open import compatible
open import progress


module barKripke {n : Level} (W : PossibleWorlds {n})
       where

open import worldDef{n}(W)
open import bar{n}{n}(W)
open import mod{n}{n}(W)


-- all the worlds above w are in the bar
K𝔹bars : Bars
K𝔹bars w bar = ∀𝕎 w (λ w' _ → bar w')


-- a Kripke bar
K𝔹 : 𝕎· → Set (lsuc n)
K𝔹 w = 𝔹 K𝔹bars w

inKripkeBar : ∀ {l} (w : 𝕎·) (f : wPred {l} w) → Set (lsuc n ⊔ l)
inKripkeBar w = Σ∈𝔹 K𝔹bars {w}

inKripkeBar' : ∀ {l} (w : 𝕎·) {g : wPred {l} w} (h : inKripkeBar w g) (f : wPredDep g) → Set (lsuc n ⊔ l)
inKripkeBar' w = Σ∈𝔹' K𝔹bars {w}


K𝔹bars⊑ : Bars⊑ K𝔹bars
K𝔹bars⊑ {w1} {w2} e bar h w' e' = w' , h w' (⊑-trans· e e') , ⊑-refl· w' , e'


K𝔹bars∩ : Bars∩ K𝔹bars
K𝔹bars∩ {w} b1 b2 bars1 bars2 w' e' = w , w , bars1 w (⊑-refl· _) , bars2 w (⊑-refl· _) , e' , e'


K𝔹bars∀ : Bars∀ K𝔹bars
K𝔹bars∀ w w' e' = e'


K𝔹In : {w : 𝕎·} (b : K𝔹 w) → 𝔹In {K𝔹bars} {w} b
K𝔹In {w} b = mk𝔹In w (⊑-refl· w) (𝔹.bars b w (⊑-refl· _))


K𝔹barsFam2 : BarsFam2 K𝔹bars
K𝔹barsFam2 {_} {w} b G i w' e' = K𝔹In b , z (fst (i (𝔹In.e1 (K𝔹In b)) (𝔹In.br (K𝔹In b))))
  where
    z : (b' : 𝔹 K𝔹bars w) → 𝔹.bar b' w'
    z (mk𝔹 bar bars ext mon) = bars w' e'


K𝔹bars∃ : Bars∃ K𝔹bars
K𝔹bars∃ {w} {b} bars ext = w , ⊑-refl· w , bars w (⊑-refl· _)



K𝔹BarsProps : BarsProps
K𝔹BarsProps =
  mkBarsProps
    K𝔹bars
    K𝔹bars⊑
    K𝔹bars∩
    K𝔹bars∀
    K𝔹barsFam2
    K𝔹bars∃

inKripkeBar-Mod : Mod
inKripkeBar-Mod = BarsProps→Mod K𝔹BarsProps


-- A few consequences
trivialK𝔹 : (w : 𝕎·) → K𝔹 w
trivialK𝔹 = 𝔹∀ {K𝔹bars} K𝔹bars∀


K𝔹all : {w : 𝕎·} (b : 𝔹 K𝔹bars w) → 𝔹.bar b w
K𝔹all {w} b = (𝔹.bars b w (⊑-refl· _))

\end{code}
