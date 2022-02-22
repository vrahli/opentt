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
open import Data.List.Membership.Propositional
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
open import getChoice
open import newChoice
open import freeze
open import mod
open import choiceExt


module openNotFollowChoice (E : Extensionality 0ℓ 3ℓ)
       where

open import worldInstanceRef

W : PossibleWorlds
W = PossibleWorldsRef

C : Choice
C = choiceRef

K : Compatible W C
K = compatibleREF

P : Progress W C K
P = progressREF

open import barOpen(W)

M : Mod W
M = inOpenBar-Mod

G : GetChoice W C K
G = getChoiceRef

N : NewChoice W C K G
N = newChoiceRef

F : Freeze W C K P G N
F = freezeREF

X : ChoiceExt W C K G
X = choiceExtRef

open import worldDef(W)
--open import bar(W)
open import mod(W)
--open import barOpen(W)
open import choiceDef{1ℓ}(C)
open import compatibleDef(W)(C)(K)
open import progressDef(W)(C)(K)(P)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import newChoiceDef(W)(C)(K)(G)(N)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

--open import barBeth(W)(C)(K)(P)
open import barI(W)(M)(C)(K)(P)
open import computation(W)(C)(K)(G)

open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)


-- TODO: if we didn't want to rely on the choice instance at all,
-- we could add to getFreeze that we have ¬ freezable c w' in the extensions
¬followChoice-open-ref-aux : (w : 𝕎·)
                             → ¬((c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                                    → □· w f --inOpenBar w f
                                    → onlyℂ∈𝕎 (Res.def r) c w
                                    → compatible· c w r
                                    → freezable· c w
                                    → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
¬followChoice-open-ref-aux w0 h =
  lower (snd (snd (snd (snd (snd q))))) (fst (snd (snd (snd (snd q)))))
  where
    r : Res{0ℓ}
    r = Resℂ₀₁

    c : Name
    c = newChoice· w0

    w : 𝕎·
    w = startNewChoice r w0

    f : wPred w
    f w' e = Lift 2ℓ (¬ freezable· c w')

    comp : compatible· c w r
    comp = startChoiceCompatible· r w0

    k : ℂ·
    k = ℂ₁·

    i : inOpenBar w f
    i w1 e1 = w2 , e2 , aw
      where
        w2 : 𝕎·
        w2 = freeze· c w1 k

        e2 : w1 ⊑· w2
        e2 = freeze⊑· c w1 k (⊑-compatible· e1 comp) λ n → inj₂ refl

        -- This we where we could modify getFreeze or add an axiom like freeze→¬freezable
        aw : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
        aw w3 e3 z = freeze→¬freezable {c} {w1} k (⊑-compatible· e1 comp) w3 e3

    oc : onlyℂ∈𝕎 (Res.def r) c w
    oc n = getChoice-startNewChoice· n r w0

    fb : freezable· c w
    fb = freezableStart· r w0

    q :  ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)
    q = h c {w} {f} {r} i oc comp fb


{--
-- We need 𝕎 to be non-empty
¬followChoice-open-ref : ¬((c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                           → inOpenBar w f
                           → isOnlyChoice∈𝕎 (Res.def r) c w
                           → compatible· c w r
                           → freezable· c w
                           → ∃𝕎 w (λ w1 e1 → isOnlyChoice∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
¬followChoice-open-ref h = {!!}
--}
\end{code}
