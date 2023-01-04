\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum

open import world


module cucleusImpliesCoversProps {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)
open import nucleus{L}(W)
open import coversProps{L}(W)

-- We postulate a covering nucleus _▶ instead of passing it as a module parameter
-- since doing it as a parameter was annoying to figure out
postulate
  _▶        : (UCSubset → UCSubset)
  j-cucleus : cucleus _▶

-- From an arbitrary covering nucleus we can get a covering relation
_◀_ : Cover
_◀_ w U = w ∈· (U ▶)

-- For ease of use we unpack all of the covering nucleus properties first

▶-well-def : well-defined _▶
▶-well-def = fst (fst j-cucleus)

▶-ext : extensive _▶
▶-ext = fst (snd (fst j-cucleus))

▶-idem : idempotent _▶
▶-idem = fst (snd (snd (fst j-cucleus)))

▶-meet-pre : meet-preserving _▶
▶-meet-pre = snd (snd (snd (fst j-cucleus)))

▶-under : undershooting _▶
▶-under = fst (snd j-cucleus)

▶-inhab : inhabited _▶
▶-inhab = snd (snd j-cucleus)

▶-mono : monotonic _▶
▶-mono = cucleus-monotonic j-cucleus

-- And now we can prove that the covering relation from a cucleus satisfies
-- all the necessary properties

◀-Cover∩ : Cover∩ _◀_
◀-Cover∩ {w} U V w◀U w◀V = snd (▶-meet-pre U V) (w◀U , w◀V)

◀-Cover∀ : Cover∀ _◀_
◀-Cover∀ w = ▶-ext (bar∀ w) (⊑-refl· w)

◀-Cover⊑ : Cover⊑ _◀_
◀-Cover⊑ {w1} {w2} e12 U w1◀U = fst (▶-well-def (U ⋒ (bar∀ w2)) (res≥ w2 U) ⋒∀≅res≥) w2◀U∩bar∀
  where
    w2◀U∩bar∀ : w2 ◀ U ⋒ (bar∀ w2)
    w2◀U∩bar∀ = ◀-Cover∩ U (bar∀ w2) (snd (U ▶) e12 w1◀U) (◀-Cover∀ w2)

    ⋒∀≅res≥ : U ⋒ (bar∀ w2) ≅ res≥ w2 U
    ⋒∀≅res≥ = (λ x → x) , (λ x → x)

◀-Cover∪ : Cover∪ _◀_
◀-Cover∪ {w} U w◀U G i = U▶⋐bar∪▶ w◀U
  where
    U⋐bar∪ : U ⋐ ((bar∪ U w◀U G i) ▶)
    U⋐bar∪ {w1} w1∈U = ▶-under (λ h → fst (i (snd h))) ((w1 , w1∈U) , fst (snd (i w1∈U)))

    U▶⋐bar∪▶ : (U ▶) ⋐ ((bar∪ U w◀U G i) ▶)
    U▶⋐bar∪▶ = ⋐-tran {U ▶} {((bar∪ U w◀U G i) ▶) ▶} {(bar∪ U w◀U G i) ▶} (▶-mono U ((bar∪ U w◀U G i) ▶) U⋐bar∪) (▶-idem (bar∪ U w◀U G i))

◀-Cover∃ : Cover∃ _◀_
◀-Cover∃ w◀U = ▶-inhab w◀U

◀-CoversProps : CoversProps
◀-CoversProps = mkCoversProps _◀_ ◀-Cover⊑ ◀-Cover∩ ◀-Cover∀ ◀-Cover∪ ◀-Cover∃

\end{code}
