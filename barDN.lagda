\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; pred ; _⊔_)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Empty


open import util
open import calculus
open import world


-- double negation
module barDN {L : Level} (W : PossibleWorlds {L})
       where

open import worldDef{L}(W)
open import bar(W)
open import mod(W)



{-----------------------------------------
 --
 -- Double Negation Bar instance
 --
 --}

------
-- A double negation bar
DN𝔹bars : Bars
DN𝔹bars w bar = ∀𝕎 w (λ w1 e1 → ¬ (¬ (Lift (lsuc(L)) (bar w1))))


DN𝔹bars⊑ : Bars⊑ DN𝔹bars
DN𝔹bars⊑ {w1} {w2} e bar h w3 e3 q = h w3 (⊑-trans· e e3) (λ (lift z) → q (lift (w3 , z , ⊑-refl· w3 , e3)))


DN𝔹bars∩ : Bars∩ DN𝔹bars
DN𝔹bars∩ b1 b2 h1 h2 w1 e1 h =
  h1 w1 e1 (λ (lift z1) → h2 w1 e1 (λ (lift z2) → h (lift (w1 , w1 , z1 , z2 , ⊑-refl· w1 , ⊑-refl· w1))))


DN𝔹bars∀ : Bars∀ DN𝔹bars
DN𝔹bars∀ w w1 e1 h = h (lift e1)


DN𝔹barsFam2 : BarsFam2 DN𝔹bars
DN𝔹barsFam2 {w} b G i w1 e1 h = {!!}


O𝔹bars∃ : Bars∃ DN𝔹bars
O𝔹bars∃ {w} {bar} bars ext = {!!}


DN𝔹BarsProps : BarsProps
DN𝔹BarsProps =
  mkBarsProps
    DN𝔹bars
    DN𝔹bars⊑
    DN𝔹bars∩
    DN𝔹bars∀
    DN𝔹barsFam2
    O𝔹bars∃

