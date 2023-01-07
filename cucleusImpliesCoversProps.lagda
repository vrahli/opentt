\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum

open import world


module cucleusImpliesCoversProps {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)
open import nucleus{L}(W)
open import coversProps{L}(W)

-- From an arbitrary covering nucleus we can get a covering relation
_◀[_]_ : 𝕎· → (UCSubset → UCSubset) → UCSubset → Set L
_◀[_]_ w j U = w ∈· (j U)

isNuclear⇒Cover∩ : {j : UCSubset → UCSubset} → isNuclear j → Cover∩ _◀[ j ]_
isNuclear⇒Cover∩ nuc U V w◀U w◀V = snd (isNuclear.meet-pre nuc U V) (w◀U , w◀V)

isNuclear⇒Cover∀ : {j : UCSubset → UCSubset} → isNuclear j → Cover∀ _◀[ j ]_
isNuclear⇒Cover∀ nuc w = isNuclear.ext nuc (bar∀ w) (⊑-refl· w)

isNuclear⇒Cover⊑ : {j : UCSubset → UCSubset} → isNuclear j → Cover⊑ _◀[ j ]_
isNuclear⇒Cover⊑ {j} nuc {w1} {w2} e12 U w1◀U =
  fst (isNuclear.well-def nuc (U ⋒ (bar∀ w2)) (res≥ w2 U) ⋒∀≅res≥) w2◀U∩bar∀
  where
    cover∩ = isNuclear⇒Cover∩ nuc
    cover∀ = isNuclear⇒Cover∀ nuc

    w2◀U∩bar∀ : w2 ◀[ j ] U ⋒ (bar∀ w2)
    w2◀U∩bar∀ = cover∩ U (bar∀ w2) (snd (j U) e12 w1◀U) (cover∀ w2)

    ⋒∀≅res≥ : U ⋒ (bar∀ w2) ≅ res≥ w2 U
    ⋒∀≅res≥ = (λ x → x) , (λ x → x)

isNuclear⇒Cover∪ : {j : UCSubset → UCSubset} → isNuclear j → Cover∪ _◀[ j ]_
isNuclear⇒Cover∪ {j} nuc {w} U w◀U G i = jU⋐j⋓Ui w◀U
  where
    mono = nucleus-monotonic nuc

    ⋓Ui : UCSubset
    ⋓Ui = bar∪ U w◀U G i

    f : Σ 𝕎· (_∈· U) → UCSubset
    f (wi , wi∈U) = fst (i wi∈U)

    jf : Σ 𝕎· (_∈· U) → UCSubset
    jf (wi , wi∈U) = j (fst (i wi∈U))

    ⋓jUi : UCSubset
    ⋓jUi = union· jf

    U⋐⋓jUi : U ⋐ ⋓jUi
    U⋐⋓jUi {wi} wi∈U = let (_ , wi◀Ui , _) = i wi∈U in (wi , wi∈U) , wi◀Ui

    ⋓jUi⋐j⋓Ui : ⋓jUi ⋐ j ⋓Ui
    ⋓jUi⋐j⋓Ui = ⋓-elim jf {j ⋓Ui} (λ x → mono (f x) ⋓Ui (⋓-intro f x))

    U⋐j⋓Ui : U ⋐ j ⋓Ui
    U⋐j⋓Ui = ⋐-tran {U} {⋓jUi} {j ⋓Ui} U⋐⋓jUi ⋓jUi⋐j⋓Ui

    jU⋐j⋓Ui : j U ⋐ j (bar∪ U w◀U G i)
    jU⋐j⋓Ui = ⋐-tran {j U} {j (j ⋓Ui)} {j ⋓Ui} (mono U (j ⋓Ui) U⋐j⋓Ui) (isNuclear.idem nuc ⋓Ui)


inhabited⇒Cover∃ : {j : UCSubset → UCSubset} → inhabited j → Cover∃ _◀[ j ]_
inhabited⇒Cover∃ inhab = inhab

isCuclear⇒CoversProps : {j : UCSubset → UCSubset} → isCuclear j → CoversProps
isCuclear⇒CoversProps {j} cuc = mkCoversProps
  _◀[ j ]_
  (isNuclear⇒Cover⊑ {j} (isCuclear.nuc cuc))
  (isNuclear⇒Cover∩ {j} (isCuclear.nuc cuc))
  (isNuclear⇒Cover∀ {j} (isCuclear.nuc cuc))
  (isNuclear⇒Cover∪ {j} (isCuclear.nuc cuc))
  (inhabited⇒Cover∃ {j} (isCuclear.inhab cuc))

\end{code}
