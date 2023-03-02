\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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


module barOpen {n : Level} (W : PossibleWorlds {n})
       where

open import worldDef(W)
open import bar(n)(W)
open import mod(n)(W)
open import nucleus(W)
open import cucleusImpliesCoverageProps(W)

{-----------------------------------------
 --
 -- Open Bar instance
 --
 --}

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

-- f holds in an open bar
inOpenBar : ∀ {l}  (w : 𝕎·) (f : wPred {l} w) → Set (n ⊔ l)
inOpenBar w f =
  ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → ∀𝕎 w2 (λ w3 e3 →
     (z : w ⊑· w3) → f w3 z)))

Σ∈𝔹→inOpenBar : ∀ {l} (w : 𝕎·) (f : wPred {l} w) → Mod.□ inOpenBar-Mod w f → inOpenBar w f
Σ∈𝔹→inOpenBar w f (b , i) w1 e1 =
  fst (𝔹.covers b w1 e1) ,
  fst (snd (𝔹.covers b w1 e1)) ,
  g
  where
    g : ∀𝕎 (fst (𝔹.covers b w1 e1)) (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    g w2 e2 z = i (⊑-trans· e1 (fst (snd (𝔹.covers b w1 e1)))) (snd (snd (𝔹.covers b w1 e1))) w2 e2 z


inOpenBar→Σ∈𝔹 : ∀ {l} (w : 𝕎·) (f : wPred {l} w) → inOpenBar w f → Mod.□ inOpenBar-Mod w f
inOpenBar→Σ∈𝔹 {l} w f i =
  mk𝔹 bar w◀U Uext , g
  where
    -- Even though the predicate may be valued in any universe `l`, we can still get the subset of worlds satisfying it.
    -- The idea is that `i` gives us the worlds satisfying the predicate along with the proof they satisfy it,
    -- but if we forget the proof exists, then we come back down to the correct universe.
    U : Subset
    U w0 = Σ 𝕎· λ w1 → Σ (w ⊑· w1) λ e1 → fst (i w1 e1) ⊑· w0

    U-UC : isUpwardsClosed U
    U-UC {w1} {w2} e12 (w3 , e01 , e41) = w3 , e01 , ⊑-trans· e41 e12

    bar : UCSubset
    bar = U , U-UC

    w◀U : O𝔹bars w bar
    w◀U w1 e1 = fst (i w1 e1) , fst (snd (i w1 e1)) , w1 , e1 , ⊑-refl· _

    Uext : {w' : 𝕎·} → w' ∈ U → w ⊑· w'
    Uext {w'} (w1 , e1 , e) = ⊑-trans· e1 (⊑-trans· (fst (snd (i w1 e1))) e)

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → w1 ∈ U → w2 ∈ U
    mon {w1} {w2} e (w0 , e0 , e') = w0 , e0 , ⊑-trans· e' e

    g : ∈𝔹 {l} {O𝔹bars} {w} (mk𝔹 bar w◀U Uext) f
    g {w'} e (w1 , e1 , e') w2 e2 z = snd (snd (i w1 e1)) w2 (⊑-trans· e' e2) z

\end{code}
