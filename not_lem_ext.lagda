\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties


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
open import freezeExt
open import progress
open import choiceBar
open import mod
open import encode


module not_lem_ext {L  : Level}
                   (W  : PossibleWorlds {L})
                   (M  : Mod W)
                   (C  : Choice)
                   (K  : Compatible W C)
                   (P  : Progress {L} W C K)
                   (G  : GetChoice {L} W C K)
                   (X  : ChoiceExt {L} W C)
                   (N  : NewChoice {L} W C K G)
                   (EC : Encode)
                   (V  : ChoiceVal W C K G X N EC)
                   (F  : Freeze {L} W C K P G N)
                   (FE : FreezeExt {L} W C K P G N F)
                   (CB : ChoiceBar W M C K P G X N EC V F)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(EC)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import freezeExtDef(W)(C)(K)(P)(G)(N)(F)(FE)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)

open import lem_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→#APPLY-#CS#⇛ℂ→C·)

open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (Resℂ)

open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (#Σchoice ; ¬∀𝕎¬equalInType-#Σchoice-freezable ; getChoice→equalInType-#Σchoice)

\end{code}


\begin{code}[hide]

¬∀𝕎¬equalInType-#Σchoice : (i : ℕ) (w : 𝕎·) (name : Name)
                         → compatible· name w Resℂ
                         → ¬ ∀𝕎 w (λ w' _ → ¬ inhType i w' (#Σchoice name ℂ₁·))
¬∀𝕎¬equalInType-#Σchoice i w name comp aw
  with freezableDec· name w
¬∀𝕎¬equalInType-#Σchoice i w name comp aw | inj₁ fb =
  ¬∀𝕎¬equalInType-#Σchoice-freezable i w name comp fb aw
¬∀𝕎¬equalInType-#Σchoice i w name comp aw | inj₂ nfb
  with ¬freezable· name w {Resℂ} comp tt nfb
... | n , aw0 = aw w (⊑-refl· w) (#PAIR (#NUM n) #AX , h1)
  where
    g1 : #APPLY (#CS name) (#NUM n) #⇛! ℂ→C· ℂ₁· at w
    g1 = →#APPLY-#CS#⇛ℂ→C· aw0

    h1 : equalInType i w (#Σchoice name ℂ₁·) (#PAIR (#NUM n) #AX) (#PAIR (#NUM n) #AX)
    h1 = getChoice→equalInType-#Σchoice i comp (sat-ℂ₁ 0) g1

\end{code}
