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


module kripkeCsNotExBar {L : Level}
                        (E : Extensionality 0ℓ 3ℓ)
       where

open import worldInstanceCS

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

V : ChoiceVal W C K G X N
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
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import newChoiceDef(W)(C)(K)(G)(N)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)



select≤ : {L : Level} {A : Set(L)} {a : A} {l : List A} {k k' : ℕ}
          → k' ≤ k
          → select k l ≡ just a
          → Σ A (λ b → select k' l ≡ just b)
select≤ {L} {A} {a} {x ∷ l} {0} {0} lek h = a , h
select≤ {L} {A} {a} {x ∷ l} {suc k} {.0} _≤_.z≤n h = x , refl
select≤ {L} {A} {a} {x ∷ l} {suc k} {.(suc _)} (_≤_.s≤s lek) h = select≤ {_} {_} {_} {l} lek h



getChoiceΣ≤ : (k : ℕ) (name : Name) (w : world) (t : ℂ·)
             → getCsChoice k name w ≡ just t
             → (k' : ℕ) → k' ≤ k
             → Σ ℂ· (λ c → getCsChoice k' name w ≡ just c)
getChoiceΣ≤ k name w t gc k' lek with getCs⊎ name w
... | inj₁ (mkcs n l r , p) rewrite p | getCs-same-name name w (mkcs n l r) p = select≤ {_} {_} {_} {l} lek gc
getChoiceΣ≤ k name w t gc k' lek | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym gc))



¬KripkeExBar : (w0 : 𝕎·)
                → ¬ ({w : 𝕎·} {f : wPred w}
                      → wPredExtIrr f
                      → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → □· w2 (↑wPred f (⊑-trans· e1 e2))))
                      → □· w f)
¬KripkeExBar w0 h = z (fst (snd q))
  where
    r : Res{0ℓ}
    r = Resℂ₀₁

    c : Name
    c = newChoice· w0

    w : 𝕎·
    w = startNewChoice r w0

    compat : compatible· c w r
    compat = startNewChoiceCompatible r w0

    m : ℕ
    m = 0

    f : wPred w
    f w' _ = ∀𝕎 w' (λ w'' _ → Lift {0ℓ} 2ℓ (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t)))

    firr : wPredExtIrr f
    firr w' e1 e2 z = z

    fcond : ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → □· w2 (↑wPred f (⊑-trans· e1 e2))))
    fcond w1 e1 = w2 , e2 , Mod.∀𝕎-□ M q
      where
        w2 : 𝕎·
        w2 = freeze· c w1 ℂ₀·

        e2 : w1 ⊑· w2
        e2 = freeze⊑· c w1 ℂ₀· (⊑-compatible· e1 compat) (λ n → inj₁ refl)

        q : ∀𝕎 w2 (↑wPred f (⊑-trans· e1 e2))
        q w3 e3 w4 e4 = lift (fst ec , snd ec , getCsChoiceCompatible c r w4 0 (fst ec) (⊑-compatible· (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) compat) (snd ec))
          where
            e : Σ ℕ (λ n → ∀𝕎 (freezeCs c w1 ℂ₀·) (λ w' _ → Lift 2ℓ (getCsChoice n c w' ≡ just ℂ₀·)))
            e = getFreezeCsAux c w1 ℂ₀· (⊑-compatible· e1 compat)

            n : ℕ
            n = fst e

            gc : getCsChoice n c w4 ≡ just ℂ₀·
            gc = lower (snd e w4 (⊑-trans· e3 e4))

            ec : Σ ℂ· (λ u → getCsChoice 0 c w4 ≡ just u)
            ec = getChoiceΣ≤ n c w4 ℂ₀· gc 0 _≤_.z≤n

    q : Σ ℂ· (λ t → getChoice· m c w ≡ just t × ·ᵣ r m t)
    q = lower (snd (h {w} {f} firr fcond) (⊑-refl· _) (K𝔹all (fst (h {w} {f} firr fcond))) w (⊑-refl· _) (⊑-refl· _) w (⊑-refl· _))

    k : ℂ·
    k = fst q

    z : getChoice· m c (startChoice· c r w0) ≡ just k → ⊥
    z x = ¬just≡nothing (trans (sym x) y)
      where
        y : getChoice· m c w ≡ nothing
        y = getCsChoice-startCsChoice-nothing m r w0 c (¬fresh∈dom𝕎 w0 (wnames w0))

\end{code}
