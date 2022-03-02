\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import mod


module typeC {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
             (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
             (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C K G) (N : NewChoice {L} W C K G)
             (F : Freeze {L} W C K P G N)
             (E : Extensionality 0ℓ (lsuc(lsuc(L))))
             (CB : ChoiceBar W M C K P G X N F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)
--open import lem_props(W)(M)(C)(K)(P)(G)(X)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
--open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)



-- A short name
Resℂ : Res
Resℂ = Resℂ₀₁


sat→equalInType-Typeℂ₀₁· : (i : ℕ) (w : 𝕎·) (k : ℂ·)
                            → Σ ℕ (λ n → ·ᵣ Resℂ n k)
                            → equalInType i w Typeℂ₀₁· (ℂ→C· k) (ℂ→C· k)
sat→equalInType-Typeℂ₀₁· i w k (n , inj₁ x) rewrite x = ℂ₀∈Typeℂ₀₁· i w
sat→equalInType-Typeℂ₀₁· i w k (n , inj₂ y) rewrite y = ℂ₁∈Typeℂ₀₁· i w



comp-Resℂ→□·-weakℂ₀₁ : {c : Name} {w : 𝕎·} (n : ℕ)
                           → compatible· c w Resℂ
                           → □· w (λ w' _ → weakℂ₀₁M w' (getT n c))
comp-Resℂ→□·-weakℂ₀₁ {c} {w} n comp = Mod.∀𝕎-□Func M aw j1
  where
    j1 : □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℂ· (λ t → getChoice· n c w'' ≡ just t × ·ᵣ Resℂ n t))))
    j1 = □·-choice· w c n Resℂ comp

    aw : ∀𝕎 w (λ w2 e2 → ∀𝕎 w2 (λ w3 _ → Lift (lsuc L) (Σ ℂ· (λ t → getChoice· n c w3 ≡ just t × ·ᵣ Resℂ n t))) → weakℂ₀₁M w2 (getT n c))
    aw w2 e2 h w3 e3 rewrite fst (snd (lower (h w3 e3))) = lift (ℂ→T t , refl , z st)
      where
        t : ℂ·
        t = fst (lower (h w3 e3))

        st : ·ᵣ Resℂ n t
        st = snd (snd (lower (h w3 e3)))
--getChoiceCompatible· c Resℂ w3 n t (⊑-compatible· (⊑-trans· e2 e3) comp) (snd (lower (h w3 e3)))

        z : (t ≡ ℂ₀· ⊎ t ≡ ℂ₁·) → (ℂ→T t ⇓! Tℂ₀ at w3 ⊎ ℂ→T t ⇓! Tℂ₁ at w3)
        z (inj₁ x) rewrite x = inj₁ (0 , refl)
        z (inj₂ x) rewrite x = inj₂ (0 , refl)



→equalInType-APPLY-CS-Typeℂ₀₁· : {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                                  → compatible· c w Resℂ
                                  → equalInType i w #NAT! a₁ a₂
                                  → equalInType i w Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-Typeℂ₀₁· {i} {w} {c} {a₁} {a₂} comp eqi =
  equalInType-local (Mod.∀𝕎-□Func M aw1' (equalInType-NAT!→ i w a₁ a₂ eqi))
  where
    aw1' : ∀𝕎 w (λ w'' e'' → #⇛!sameℕ {--#strongMonEq--} w'' a₁ a₂ → equalInType i w'' Typeℂ₀₁· (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂))
    aw1' w1 e1 (n , c₁ , c₂) = equalInType-#⇛-LR-rev (#⇛!-APPLY-CS {w1} {a₁} {#NUM n} c c₁) (#⇛!-APPLY-CS {w1} {a₂} {#NUM n} c c₂) eqj
      where
        j2 : □· w1 (λ w' _ → weakℂ₀₁M w' (getT n c))
        j2 = comp-Resℂ→□·-weakℂ₀₁ n (⊑-compatible· e1 comp)

        eqj : ∈Type i w1 Typeℂ₀₁· (#APPLY (#CS c) (#NUM n))
        eqj = →∈Typeℂ₀₁· i j2

\end{code}
