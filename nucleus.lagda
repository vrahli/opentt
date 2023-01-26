\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum

open import world

module nucleus {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)

-- The frame of subsets of the Kripke frame

Subset : Set (lsuc L)
Subset = 𝕎· → Set L

_∈_ : 𝕎· → Subset → Set L
_∈_ w U = U w
infix 20 _∈_

_⊆_ : Subset → Subset → Set L
_⊆_ U V = {w : 𝕎·} → w ∈ U → w ∈ V
infix 21 _⊆_

⊆-refl : (U : Subset) → U ⊆ U
⊆-refl _ w∈U = w∈U

⊆-tran : {U V W : Subset} → U ⊆ V → V ⊆ W → U ⊆ W
⊆-tran U⊆V V⊆W w∈U = V⊆W (U⊆V w∈U)

_≃_ : Subset → Subset → Set L
_≃_ X Y = X ⊆ Y × Y ⊆ X
infix 21 _≃_

≃-refl : (U : Subset) → U ≃ U
≃-refl U = ⊆-refl U , ⊆-refl U

≃-tran : {U V W : Subset} → U ≃ V → V ≃ W → U ≃ W
≃-tran {_} {V} {_} (U⊆V , V⊆U) (V⊆W , W⊆V) = ⊆-tran {V = V} U⊆V V⊆W , ⊆-tran {V = V} W⊆V V⊆U

_∩_ : Subset → Subset → Subset
_∩_ U V w = w ∈ U × w ∈ V
infix 22 _∩_

∩-intro : {U V W : Subset} → W ⊆ U → W ⊆ V → W ⊆ U ∩ V
∩-intro W⊆U W⊆V w∈W = W⊆U w∈W , W⊆V w∈W

∩-elim-l : {U V : Subset} → U ∩ V ⊆ U
∩-elim-l = fst

∩-elim-r : {U V : Subset} → U ∩ V ⊆ V
∩-elim-r = snd

∩-implies-⊆ : {U V : Subset} → U ≃ U ∩ V → U ⊆ V
∩-implies-⊆ {U} {V} (U⊆U∩V , _) = ⊆-tran {U} {U ∩ V} {V} U⊆U∩V (∩-elim-r {U} {V})

⊆-implies-∩ : {U V : Subset} → U ⊆ V → U ≃ U ∩ V
⊆-implies-∩ {U} {V} U⊆V = ∩-intro {U} (⊆-refl U) U⊆V , ∩-elim-l {U} {V}

union : {I : Set L} (f : I → Subset) → Subset
union {I} f w = Σ[ i ∈ I ] (w ∈ f i)

syntax union {I} (λ i → M) = ∪[ i ∈ I ] M

∪-intro : {I : Set L} (f : I → Subset) (i : I) → f i ⊆ union f
∪-intro f i w∈fi = (i , w∈fi)

∪-elim : {I : Set L} (f : I → Subset) {U : Subset} → ((i : I) → f i ⊆ U) → union f ⊆ U
∪-elim f g (i , w∈fi) = g i w∈fi

-- The frame of upward closed subsets of the Kripke frame

isUpwardsClosed : Subset → Set L
isUpwardsClosed U = {w1 w2 : 𝕎·} → w1 ⊑· w2 → w1 ∈ U → w2 ∈ U

UCSubset : Set (lsuc L)
UCSubset = Σ Subset isUpwardsClosed

_∈·_ : 𝕎· → UCSubset → Set L
_∈·_ w (U , _) = w ∈ U
infix 20 _∈·_

_⋐_ : UCSubset → UCSubset → Set L
_⋐_ U V = {w : 𝕎·} → w ∈· U → w ∈· V
infix 21 _⋐_

⋐-refl : {U : UCSubset} → U ⋐ U
⋐-refl {U , _} = ⊆-refl U

⋐-tran : {U V W : UCSubset} → U ⋐ V → V ⋐ W → U ⋐ W
⋐-tran {U , _} {V , _} {W , _} = ⊆-tran {U} {V} {W}

_≅_ : UCSubset → UCSubset → Set L
_≅_ U V = U ⋐ V × V ⋐ U
infix 21 _≅_

≅-refl : (U : UCSubset) → U ≅ U
≅-refl (U , _) = ≃-refl U

≅-tran : {U V W : UCSubset} → U ≅ V → V ≅ W → U ≅ W
≅-tran {_} {V , _} {_} = ≃-tran {V = V}

_⋒_ : UCSubset → UCSubset → UCSubset
_⋒_ (U , U-is-UC) (V , V-is-UC) = U ∩ V , λ e (w∈U , w∈V) → U-is-UC e w∈U , V-is-UC e w∈V
infix 22 _⋒_

⋒-elim-l : {U V : UCSubset} → U ⋒ V ⋐ U
⋒-elim-l {U , _} {V , _} = ∩-elim-l {U} {V}

⋒-elim-r : {U V : UCSubset} → U ⋒ V ⋐ V
⋒-elim-r {U , _} {V , _} = ∩-elim-r {U} {V}

⋒-intro : {U V W : UCSubset} → W ⋐ U → W ⋐ V → W ⋐ U ⋒ V
⋒-intro {U , _} {V , _} {W , _} = ∩-intro {U} {V} {W}

⋒-implies-⋐ : {U V : UCSubset} → U ≅ U ⋒ V → U ⋐ V
⋒-implies-⋐ {U , _} {V , _} = ∩-implies-⊆ {U} {V}

⋐-implies-⋒ : {U V : UCSubset} → U ⋐ V → U ≅ U ⋒ V
⋐-implies-⋒ {U , _} {V , _} = ⊆-implies-∩ {U} {V}

union· : {I : Set L} (f : I → UCSubset) → UCSubset
union· {I} f = ∪[ i ∈ I ] (fst (f i)) , λ e12 (i , w1∈fi) → i , snd (f i) e12 w1∈fi

syntax union· {I} (λ i → M) = ⋓[ i ∈ I ] M

⋓-intro : {I : Set L} (f : I → UCSubset) (i : I) → f i ⋐ union· f
⋓-intro f = ∪-intro (λ i → fst (f i))

⋓-elim : {I : Set L} (f : I → UCSubset) {U : UCSubset} → ((i : I) → f i ⋐ U) → union· f ⋐ U
⋓-elim f = ∪-elim (λ i → fst (f i))

-- Definition of a nucleus on the frame of upward closed subsets

well-defined : (UCSubset → UCSubset) → Set (lsuc L)
well-defined j = (U V : UCSubset) → U ≅ V → j U ≅ j V

extensive : (UCSubset → UCSubset) → Set (lsuc L)
extensive j = (U : UCSubset) → U ⋐ j U

idempotent : (UCSubset → UCSubset) → Set (lsuc L)
idempotent j = (U : UCSubset) → j (j U) ⋐ j U

meet-preserving : (UCSubset → UCSubset) → Set (lsuc L)
meet-preserving j = (U V : UCSubset) → j (U ⋒ V) ≅ j U ⋒ j V

monotonic : (UCSubset → UCSubset) → Set (lsuc L)
monotonic j = (U V : UCSubset) → U ⋐ V → j U ⋐ j V

meet-preserving⇒monotonic : {j : UCSubset → UCSubset} → well-defined j → meet-preserving j → monotonic j
meet-preserving⇒monotonic {j} well-def meet-pre U V U⋐V = ⋒-implies-⋐ {j U} {j V}
  (≅-tran {j U} {j (U ⋒ V)} {j U ⋒ j V} (well-def U (U ⋒ V) (⋐-implies-⋒ {U} {V} U⋐V)) (meet-pre U V))

inhabited : (UCSubset → UCSubset) → Set (lsuc L)
inhabited j = {w : 𝕎· } (U : UCSubset) → w ∈· j U → Σ[ w' ∈ 𝕎· ] w' ∈· U


record isNuclear (j : UCSubset → UCSubset) : Set (lsuc L) where
  constructor mkNucleus
  field
    well-def : well-defined j
    ext      : extensive j
    idem     : idempotent j
    meet-pre : meet-preserving j

-- A c(overing n)ucleus
record isCuclear (j : UCSubset → UCSubset) : Set (lsuc L) where
  constructor mkCucleus
  field
    inhab : inhabited j
    nuc   : isNuclear j

nucleus-monotonic : {j : UCSubset → UCSubset} → isNuclear j → monotonic j
nucleus-monotonic {j} nuc = meet-preserving⇒monotonic {j} (isNuclear.well-def nuc) (isNuclear.meet-pre nuc)

cucleus-monotonic : {j : UCSubset → UCSubset} → isCuclear j → monotonic j
cucleus-monotonic {j} cuc = nucleus-monotonic (isCuclear.nuc cuc)

\end{code}
