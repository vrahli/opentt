\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


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
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import Data.Maybe
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import mod


module kripkeCsNotRetrieving {L : Level}
                             (E0 : Extensionality 0ℓ 0ℓ)
                             (E : Extensionality 0ℓ 3ℓ)
       where

open import encoding3(E0)

open import worldInstanceCS(E0)

W : PossibleWorlds
W = PossibleWorldsCS

C : Choice
C = choiceCS

K : Compatible W C
K = compatibleCS

P : Progress W C K
P = progressCS

open import barKripke(W)

M : Mod W
M = BarsProps→Mod W K𝔹BarsProps


G : GetChoice W C K
G = getChoiceCS

N : NewChoice W C K G
N = newChoiceCS

F : Freeze W C K P G N
F = freezeCS

X : ChoiceExt W C
X = choiceExtCS

V : ChoiceVal W C K G X N enc
V = choiceValCS

open import worldDef(W)
open import bar(W)
open import mod(W)
open import barOpen(W)
open import choiceDef{1ℓ}(C)
open import compatibleDef(W)(C)(K)
open import progressDef(W)(C)(K)(P)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(enc)(V)
open import newChoiceDef(W)(C)(K)(G)(N)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)



-- retrieving holds for references (see modInstanceKripkeRefBool) but not for choice sequences
¬KripkeChoice : (w0 : 𝕎·)
                → ¬ ((w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                      → compatible· c w r
                      → □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} 2ℓ (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t)))))
¬KripkeChoice w0 h = z (fst (snd q))
  where
    r : Res{0ℓ}
    r = Resℂ₀₁

    c : Name
    c = newChoice· w0

    w : 𝕎·
    w = startNewChoice r w0

    comp : compatible· c w r
    comp = startNewChoiceCompatible r w0

    m : ℕ
    m = 0

    q : Σ ℂ· (λ t → getChoice· m c w ≡ just t × ·ᵣ r m t)
    q = lower (snd (h w c m r comp) (⊑-refl· _) (K𝔹all (fst (h w c m r comp))) w (⊑-refl· _) (⊑-refl· _) w (⊑-refl· _))

    k : ℂ·
    k = fst q

    z : getChoice· m c (startChoice· c r w0) ≡ just k → ⊥
    z x = ¬just≡nothing (trans (sym x) y)
      where
        y : getChoice· m c w ≡ nothing
        y = getCsChoice-startCsChoice-nothing m r w0 c (¬fresh∈dom𝕎 w0 (wnames w0))

\end{code}
