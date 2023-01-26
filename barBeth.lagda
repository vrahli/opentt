\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc ; _⊔_ to _∨_)
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
open import choice
open import compatible
open import progress


-- Choice is only needed for Beth bars to build an infinite sequence of worlds
module barBeth {L : Level} (W : PossibleWorlds {L ∨ 1ℓ})
               (C : Choice) (M : Compatible {L ∨ 1ℓ} W C) (P : Progress {L ∨ 1ℓ} W C M)
       where
open import worldDef{L ∨ 1ℓ}(W)
open import bar{L ∨ 1ℓ}{L ∨ 1ℓ}(W)
open import mod{L ∨ 1ℓ}{L ∨ 1ℓ}(W)
open import nucleus{L ∨ 1ℓ}(W)
open import cucleusImpliesCoverageProps{L ∨ 1ℓ}(W)

-- Those are only needed by the Beth instance
open import choiceDef{L}(C)
open import compatibleDef(W)(C)(M)
open import progressDef(W)(C)(M)(P)


{-----------------------------------------
 --
 -- Beth Bar instance -- defined from infinite sequences
 --
 --}
record BarredChain (bar : Subset) {w : 𝕎·} (c : chain w) : Set (L ∨ 1ℓ) where
  constructor mkBarredChain
  field
    w'  : 𝕎·
    b   : bar w'
    n   : ℕ
    ext : w' ⊑· chain.seq c n


IS𝔹bars : Coverage
IS𝔹bars w bar = (c : pchain w) → BarredChain (fst bar) (pchain.c c)

-- Open Coverage give a nucleus (when restricted to upward closed subsets)
j : UCSubset → UCSubset
j U = (λ w → IS𝔹bars w U) , U▶-UC
  where
    U▶-UC : isUpwardsClosed (λ w → IS𝔹bars w U)
    U▶-UC w1⊑w2 w1◀U c = let mkBarredChain w3 w3∈U n w3⊑cn = w1◀U (pchain⊑ w1⊑w2 c)
                          in mkBarredChain w3 w3∈U n w3⊑cn


IS𝔹-mono : (U V : UCSubset) → U ⋐ V → j U ⋐ j V
IS𝔹-mono U V U⋐V w◀U c = let mkBarredChain w' w'∈U n w'⊑cn = w◀U c
                          in mkBarredChain w' (U⋐V w'∈U) n w'⊑cn

IS𝔹-well-defined : well-defined j
IS𝔹-well-defined = λ U V (U⋐V , V⋐U) → IS𝔹-mono U V U⋐V , IS𝔹-mono V U V⋐U

IS𝔹-extensive : extensive j
IS𝔹-extensive (U , U-UC) {w} w∈U c = mkBarredChain w w∈U 0 (chain.init (pchain.c c))

IS𝔹-idempotent : idempotent j
IS𝔹-idempotent U {w} w◀◀U c = let mkBarredChain w1 w1◀U n w1⊑cn   = w◀◀U c
                                  mkBarredChain w2 w2∈U m w2⊑cm+n = w1◀U (truncatePChain {w} {c} w1⊑cn)
                               in mkBarredChain w2 w2∈U (m + n) w2⊑cm+n

IS𝔹-meet-preserving : meet-preserving j
IS𝔹-meet-preserving U V = jU⋒V⋐jU⋒jV , jU⋒jV⋐jU⋒V
  where
    jU⋒V⋐jU⋒jV : j (U ⋒ V) ⋐ j U ⋒ j V
    jU⋒V⋐jU⋒jV = ⋒-intro {j U} {j V} {j (U ⋒ V)} (IS𝔹-mono (U ⋒ V) U (⋒-elim-l {U} {V}))
                                                 (IS𝔹-mono (U ⋒ V) V (⋒-elim-r {U} {V}))

    jU⋒jV⋐jU⋒V : j U ⋒ j V ⋐ j (U ⋒ V)
    jU⋒jV⋐jU⋒V {w} (w◀U , w◀V) c = let mkBarredChain w1 w1∈U n w1⊑cn   = w◀U c
                                       mkBarredChain w2 w2∈V m w2⊑cm+n = w◀V (truncatePChain {w} {c} {n} {w} (pchain⊑n n c))
                                       cm+n   = chain.seq (pchain.c c) (m + n)
                                       cm+n∈U = snd U (⊑-trans· w1⊑cn (≤→pchain⊑ c (m≤n+m n m))) w1∈U
                                       cm+n∈V = snd V w2⊑cm+n w2∈V
                                    in mkBarredChain cm+n  (cm+n∈U , cm+n∈V) (m + n) (⊑-refl· cm+n)

IS𝔹-inhabited : inhabited j
IS𝔹-inhabited {w} U w◀U = let mkBarredChain w' w'∈U _ _ = w◀U (𝕎→pchain w) in w' , w'∈U

IS𝔹-cucleus : isCuclear j
IS𝔹-cucleus = mkCucleus IS𝔹-inhabited (mkNucleus IS𝔹-well-defined IS𝔹-extensive IS𝔹-idempotent IS𝔹-meet-preserving)

IS𝔹CoverageProps : CoverageProps
IS𝔹CoverageProps = isCuclear⇒CoverageProps IS𝔹-cucleus

-- a Beth bar where all infinite sequences are barred
IS𝔹 : 𝕎· → Set (2ℓ ∨ lsuc L)
IS𝔹 w = 𝔹 IS𝔹bars w

inBethBar : ∀ {r} (w : 𝕎·) (f : wPred {r} w) → Set (2ℓ ∨ lsuc L ∨ r)
inBethBar w = Σ∈𝔹 IS𝔹bars {w}

inBethBar' : ∀ {r} (w : 𝕎·) {g : wPred {r} w} (h : inBethBar w g) (f : wPredDep g) → Set (2ℓ ∨ lsuc L ∨ r)
inBethBar' w = Σ∈𝔹' IS𝔹bars {w}

inBethBar-Mod : Mod
inBethBar-Mod = CoverageProps→Mod IS𝔹CoverageProps

trivialIS𝔹 : (w : 𝕎·) → IS𝔹 w
trivialIS𝔹 = 𝔹∀ {IS𝔹bars} (CoverageProps.all IS𝔹CoverageProps)

inIS𝔹 : ∀ {r} {w : 𝕎·} (b : IS𝔹 w) (f : wPred {r} w) → Set (L ∨ 1ℓ ∨ r)
inIS𝔹 = ∈𝔹 {_} {IS𝔹bars}

\end{code}
