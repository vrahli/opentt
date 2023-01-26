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
open import nucleus{n}(W)
open import cucleusImpliesCoverageProps{n}(W)


-- all the worlds above w are in the bar
K𝔹bars : Coverage
K𝔹bars w bar = ∀𝕎 w (λ w' _ → w' ∈· bar)

j : UCSubset → UCSubset
j U = (λ w → K𝔹bars w U) , λ w1⊑w2 w1◀U w3 w2⊑w3 → w1◀U w3 (⊑-trans· w1⊑w2 w2⊑w3)

K𝔹-mono : (U V : UCSubset) → U ⋐ V → j U ⋐ j V
K𝔹-mono U V U⋐V w◀U w1 w⊑w1 = U⋐V (w◀U w1 w⊑w1)

K𝔹-well-defined : well-defined j
K𝔹-well-defined = λ U V (U⋐V , V⋐U) → K𝔹-mono U V U⋐V , K𝔹-mono V U V⋐U

K𝔹-extensive : extensive j
K𝔹-extensive (U , U-UC) w∈U w1 w⊑w1 = U-UC w⊑w1 w∈U

K𝔹-idempotent : idempotent j
K𝔹-idempotent U w◀◀U w1 w⊑w1 = (w◀◀U w1 w⊑w1) w1 (⊑-refl· w1)

K𝔹-meet-preserving : meet-preserving j
K𝔹-meet-preserving U V = jU⋒V⋐jU⋒jV , jU⋒jV⋐jU⋒V
  where
    jU⋒V⋐jU⋒jV : j (U ⋒ V) ⋐ j U ⋒ j V
    jU⋒V⋐jU⋒jV = ⋒-intro {j U} {j V} {j (U ⋒ V)} (K𝔹-mono (U ⋒ V) U (⋒-elim-l {U} {V}))
                                                 (K𝔹-mono (U ⋒ V) V (⋒-elim-r {U} {V}))

    jU⋒jV⋐jU⋒V : j U ⋒ j V ⋐ j (U ⋒ V)
    jU⋒jV⋐jU⋒V (w◀U , w◀V) w1 w⊑w1 = w◀U w1 w⊑w1 , w◀V w1 w⊑w1

K𝔹-inhabited : inhabited j
K𝔹-inhabited {w} U w◀U = w , w◀U w (⊑-refl· w)

K𝔹-cucleus : isCuclear j
K𝔹-cucleus = mkCucleus K𝔹-inhabited (mkNucleus K𝔹-well-defined K𝔹-extensive K𝔹-idempotent K𝔹-meet-preserving)

K𝔹CoverageProps : CoverageProps
K𝔹CoverageProps = isCuclear⇒CoverageProps K𝔹-cucleus

inKripkeBar-Mod : Mod
inKripkeBar-Mod = CoverageProps→Mod K𝔹CoverageProps


-- a Kripke bar
K𝔹 : 𝕎· → Set (lsuc n)
K𝔹 w = 𝔹 K𝔹bars w

-- A few consequences
trivialK𝔹 : (w : 𝕎·) → K𝔹 w
trivialK𝔹 = 𝔹∀ {K𝔹bars} (CoverageProps.all K𝔹CoverageProps)

K𝔹all : {w : 𝕎·} (b : 𝔹 K𝔹bars w) → w ∈· 𝔹.U b
K𝔹all {w} b = (𝔹.covers b w (⊑-refl· _))

\end{code}
