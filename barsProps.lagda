\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum

open import world


module barsProps {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)
open import nucleus{L}(W)

Cover : Set(lsuc(L))
Cover = 𝕎· → UCSubset → Set(L)

{-- Intersection --}

-- The original intersection was given by the following
--     bar∩ : Br → Br → Br
--     bar∩ b1 b2 w0 = Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → b1 w1 × b2 w2 × w1 ⊑· w0 × w2 ⊑· w0))
-- As we are only working with monotone bars, we can simply use set intersection.

Cover∩ : Cover → Set(lsuc(L))
Cover∩ _◀_ =
  {w : 𝕎·} (U V : UCSubset)
  → w ◀ U
  → w ◀ V
  → w ◀ (U ⋒ V)

{-- Monotonicity --}

-- The original restriction was given by
--    bar⊑ : 𝕎· → Br  → Br
--    bar⊑ w' bar w0 = Σ 𝕎· (λ w1 → bar w1 × w1 ⊑· w0 × w' ⊑· w0)
-- Since we are working with monotone bars though we can use instead

res≥ : 𝕎· → UCSubset → UCSubset
res≥ w0 (U , U-UC) = (λ w1 → w1 ∈ U × w0 ⊑· w1)
                   , (λ e12 (w1∈U , e01)→ U-UC e12 w1∈U , ⊑-trans· e01 e12)

Bars⊑ : Cover → Set(lsuc(L))
Bars⊑ _◀_ =
  {w1 w2 : 𝕎·} (e : w1 ⊑· w2) (U : UCSubset)
  → w1 ◀ U
  → w2 ◀ res≥ w2 U

{-- Top --}
bar∀ : 𝕎· → UCSubset
bar∀ w0 = w0 ⊑·_ , λ e12 e01 → ⊑-trans· e01 e12

-- With the original type of Cover being in Set(lsuc(lsuc(L))), this would be a universe higher
Bars∀ : Cover → Set(L)
Bars∀ _◀_ = (w : 𝕎·) → w ◀ (bar∀ w)

--record BarsProps : Set(lsuc(L)) where
--  constructor mkBarsProps
--  field
--    bars  : Bars
--    mon   : Bars⊑ bars
--    isect : Bars∩ bars
--    all   : Bars∀ bars    -- top element
--    fam2  : BarsFam2 bars -- arbitrary unions
--    ex    : Bars∃ bars    -- bars are non-empty

\end{code}
