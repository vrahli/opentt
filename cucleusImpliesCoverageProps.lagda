\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Sum

open import world


module cucleusImpliesCoverageProps {n : Level} (W : PossibleWorlds {n})
       where
open import worldDef(W)
open import nucleus(W)
open import bar(n)(W)

-- From an arbitrary covering nucleus we can get a covering relation
_◀[_]_ : 𝕎· → (UCSubset → UCSubset) → UCSubset → Set n
_◀[_]_ w j U = w ∈· (j U)

isNuclear⇒Coverage∩ : {j : UCSubset → UCSubset} → isNuclear j → Coverage∩ _◀[ j ]_
isNuclear⇒Coverage∩ nuc U V w◀U w◀V = snd (isNuclear.meet-pre nuc U V) (w◀U , w◀V)

isNuclear⇒Coverage∀ : {j : UCSubset → UCSubset} → isNuclear j → Coverage∀ _◀[ j ]_
isNuclear⇒Coverage∀ nuc w = isNuclear.ext nuc (bar∀ w) (⊑-refl· w)

isNuclear⇒Coverage⊑ : {j : UCSubset → UCSubset} → isNuclear j → Coverage⊑ _◀[ j ]_
isNuclear⇒Coverage⊑ {j} nuc {w1} {w2} e12 U w1◀U =
  fst (isNuclear.well-def nuc (U ⋒ (bar∀ w2)) (res≥ w2 U) ⋒∀≅res≥) w2◀U∩bar∀
  where
    cover∩ = isNuclear⇒Coverage∩ nuc
    cover∀ = isNuclear⇒Coverage∀ nuc

    w2◀U∩bar∀ : w2 ◀[ j ] U ⋒ (bar∀ w2)
    w2◀U∩bar∀ = cover∩ U (bar∀ w2) (snd (j U) e12 w1◀U) (cover∀ w2)

    ⋒∀≅res≥ : U ⋒ (bar∀ w2) ≅ res≥ w2 U
    ⋒∀≅res≥ = (λ x → x) , (λ x → x)

isNuclear⇒Coverage∪ : {j : UCSubset → UCSubset} → isNuclear j → Coverage∪ _◀[ j ]_
isNuclear⇒Coverage∪ {j} nuc {_} {w} (mk𝔹 U w◀U Uext) G i = jU⋐j⋓Ui w◀U
  where
    b    = mk𝔹 U w◀U Uext
    mono = nucleus-monotonic nuc

    ⋓Ui : UCSubset
    ⋓Ui = bar∪ b G i

    f : 𝔹In b → UCSubset
    f ind = 𝔹.U (fst (i ind))

    jf : 𝔹In b → UCSubset
    jf ind = j (f ind)

    ⋓jUi : UCSubset
    ⋓jUi = union· jf

    U⋐⋓jUi : U ⋐ ⋓jUi
    U⋐⋓jUi {wi} wi∈U = let (mk𝔹 Ui wi◀Ui _ , _) = i (mk𝔹In wi wi∈U) in (mk𝔹In wi wi∈U) , wi◀Ui

    ⋓jUi⋐j⋓Ui : ⋓jUi ⋐ j ⋓Ui
    ⋓jUi⋐j⋓Ui = ⋓-elim jf {j ⋓Ui} (λ x → mono (f x) ⋓Ui (⋓-intro f x))

    U⋐j⋓Ui : U ⋐ j ⋓Ui
    U⋐j⋓Ui = ⋐-tran {U} {⋓jUi} {j ⋓Ui} U⋐⋓jUi ⋓jUi⋐j⋓Ui

    jU⋐j⋓Ui : j U ⋐ j ⋓Ui
    jU⋐j⋓Ui = ⋐-tran {j U} {j (j ⋓Ui)} {j ⋓Ui} (mono U (j ⋓Ui) U⋐j⋓Ui) (isNuclear.idem nuc ⋓Ui)

inhabited⇒Coverage∃ : {j : UCSubset → UCSubset} → inhabited j → Coverage∃ _◀[ j ]_
inhabited⇒Coverage∃ inhab {w} {U}  = inhab U

isCuclear⇒CoverageProps : {j : UCSubset → UCSubset} → isCuclear j → CoverageProps
isCuclear⇒CoverageProps {j} cuc = mkCoverageProps
  _◀[ j ]_
  (isNuclear⇒Coverage⊑ {j} (isCuclear.nuc cuc))
  (isNuclear⇒Coverage∩ {j} (isCuclear.nuc cuc))
  (isNuclear⇒Coverage∀ {j} (isCuclear.nuc cuc))
  (isNuclear⇒Coverage∪ {j} (isCuclear.nuc cuc))
  (inhabited⇒Coverage∃ {j} (isCuclear.inhab cuc))

\end{code}
