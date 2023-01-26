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


module barOpen {n : Level} (W : PossibleWorlds {n})
       where

open import worldDef{n}(W)
open import bar{n}{n}(W)
open import mod{n}{n}(W)
open import nucleus{n}(W)
open import cucleusImpliesCoverageProps{n}(W)

{-----------------------------------------
 --
 -- Open Bar instance
 --
 --}

------
-- An open bar
O𝔹bars : Coverage
O𝔹bars w bar = ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 _ → w2 ∈· bar))


-- Open Coverage give a nucleus (when restricted to upward closed subsets)
j : UCSubset → UCSubset
j U = (λ w → O𝔹bars w U) , (λ w1⊑w2 w1◀U w3 w2⊑w3 → w1◀U w3 (⊑-trans· w1⊑w2 w2⊑w3))

O𝔹-mono : (U V : UCSubset) → U ⋐ V → j U ⋐ j V
O𝔹-mono U V U⋐V w◀U w1 w⊑w1 = let (w2 , w1⊑w2 , w2∈U) = w◀U w1 w⊑w1 in w2 , w1⊑w2 , U⋐V w2∈U

O𝔹-well-defined : well-defined j
O𝔹-well-defined = λ U V (U⋐V , V⋐U) → O𝔹-mono U V U⋐V , O𝔹-mono V U V⋐U

O𝔹-extensive : extensive j
O𝔹-extensive (U , U-UC) w∈U w1 w⊑w1 = w1 , ⊑-refl· w1 , U-UC w⊑w1 w∈U

O𝔹-idempotent : idempotent j
O𝔹-idempotent U w◀◀U w1 w⊑w1 = let (w2 , w1⊑w2 , w2◀U) = w◀◀U w1 w⊑w1
                                   (w3 , w2⊑w3 , w3∈U) = w2◀U w2 (⊑-refl· w2)
                                in (w3 , ⊑-trans· w1⊑w2 w2⊑w3 , w3∈U )

O𝔹-meet-preserving : meet-preserving j
O𝔹-meet-preserving U V = jU⋒V⋐jU⋒jV , jU⋒jV⋐jU⋒V
  where
    jU⋒V⋐jU⋒jV : j (U ⋒ V) ⋐ j U ⋒ j V
    jU⋒V⋐jU⋒jV = ⋒-intro {j U} {j V} {j (U ⋒ V)} (O𝔹-mono (U ⋒ V) U (⋒-elim-l {U} {V}))
                                                 (O𝔹-mono (U ⋒ V) V (⋒-elim-r {U} {V}))

    jU⋒jV⋐jU⋒V : j U ⋒ j V ⋐ j (U ⋒ V)
    jU⋒jV⋐jU⋒V (w◀U , w◀V) w1 w⊑w1 = let U-UC = snd U
                                         (w2 , w1⊑w2 , w2∈U) = w◀U w1 w⊑w1
                                         (w3 , w2⊑w3 , w3∈V) = w◀V w2 (⊑-trans· w⊑w1 w1⊑w2)
                                      in w3 , ⊑-trans· w1⊑w2 w2⊑w3 , U-UC w2⊑w3 w2∈U , w3∈V

O𝔹-inhabited : inhabited j
O𝔹-inhabited {w} U w◀U = let (w1 , _ , w1∈U) = w◀U w (⊑-refl· w) in w1 , w1∈U

O𝔹-cucleus : isCuclear j
O𝔹-cucleus = mkCucleus O𝔹-inhabited (mkNucleus O𝔹-well-defined O𝔹-extensive O𝔹-idempotent O𝔹-meet-preserving)

O𝔹CoverageProps : CoverageProps
O𝔹CoverageProps = isCuclear⇒CoverageProps O𝔹-cucleus

inOpenBar-Mod : Mod
inOpenBar-Mod = CoverageProps→Mod O𝔹CoverageProps

O𝔹 : 𝕎· → Set (lsuc n)
O𝔹 w = 𝔹 O𝔹bars w

\end{code}
