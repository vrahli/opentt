\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum


open import world

module coversPropsImplyCucleus {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)
open import nucleus{L}(W)
open import coversProps{L}(W)

postulate
  props : CoversProps

_◀_ : Cover
_◀_ = CoversProps._◁_ props

mon : Cover⊑ _◀_
mon = CoversProps.mon props

isect : Cover∩ _◀_
isect = CoversProps.isect props

all : Cover∀ _◀_
all = CoversProps.all props

fam2 : Cover∪ _◀_
fam2 = CoversProps.fam2 props

ex : Cover∃ _◀_
ex = CoversProps.ex props

-- Now we show that a covering relation satisfying coversProps gives a cucleus

▶-UCSubset→UCSubset : {U : UCSubset} →  isUpwardsClosed (_◀ U)
▶-UCSubset→UCSubset {U} {w1} {w2} w1⊑w2 w1◀U = {!!}
  where
    w2◀resU : w2 ◀ res≥ w2 U
    w2◀resU = mon w1⊑w2 U w1◀U

_▶ : UCSubset → UCSubset
_▶ U = (_◀ U) , ▶-UCSubset→UCSubset

▶-well-def : well-defined _▶
▶-well-def U V (U⋐V , V⋐U) = {!!}

▶-ext : extensive _▶
▶-ext U {w} w∈U = {!!}
  where
    G : {w' : 𝕎·} (w⊑w' : w' ∈· (bar∀ w)) (V : UCSubset) → w' ◀ V → Set(L)
    G w⊑w' V w'◀V = ⊤

    i : {w' : 𝕎·} (w⊑w' : w' ∈· (bar∀ w)) → Σ UCSubset (λ V → Σ (w' ◀ V) (λ w'◀V → G w⊑w' V w'◀V))
    i w⊑w' = U , {!!} , {!!}

    bar : UCSubset
    bar = bar∪ (bar∀ w) (all w) G i

    w◀bar : w ◀ bar
    w◀bar = fam2 (bar∀ w) (all w) G i


▶-idem : idempotent _▶
▶-idem U {w} w∈U▶▶ = fst (▶-well-def bar U bar≅U) w◀bar
  where
    G : {w' : 𝕎·} (w'∈U : w' ∈· (U ▶)) (V : UCSubset) → w' ◀ V → Set(L)
    G _ V _ = ⊤

    i : {w' : 𝕎·} (w'∈U : w' ∈· (U ▶)) → Σ UCSubset (λ V → Σ (w' ◀ V) (λ w'◀V → G w'∈U V w'◀V))
    i w'◀U = U , w'◀U , tt

    bar : UCSubset
    bar = bar∪ (U ▶) w∈U▶▶ G i

    w◀bar : w ◀ bar
    w◀bar = fam2 (U ▶) w∈U▶▶ G i

    bar⋐U : bar ⋐ U
    bar⋐U {w0} ((w1 , w1◀U) , w0∈U) = w0∈U

    U⋐bar : U ⋐ bar
    U⋐bar {w0} w0∈U = ex w∈U▶▶ , w0∈U

    bar≅U : bar ≅ U
    bar≅U = bar⋐U , U⋐bar

▶-meet-pre : meet-preserving _▶
▶-meet-pre U V = U⋒V▶⋐U▶⋒V▶ , U▶⋒V▶⋐U⋒V▶
  where
    U⋒V▶⋐U▶⋒V▶ : ((U ⋒ V) ▶) ⋐ (U ▶) ⋒ (V ▶)
    U⋒V▶⋐U▶⋒V▶ = {!!}

    U▶⋒V▶⋐U⋒V▶ : (U ▶) ⋒ (V ▶) ⋐ ((U ⋒ V) ▶)
    U▶⋒V▶⋐U⋒V▶ (w◀U , w◀V) = isect U V w◀U w◀V

▶-inhab : inhabited _▶
▶-inhab U = ex

\end{code}
