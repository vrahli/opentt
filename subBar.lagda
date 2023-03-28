\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
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
open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

open import util
open import calculus
open import world
open import choice
open import compatible
open import progress
--open import bar
open import mod

module subBar {L : Level} (W : PossibleWorlds {L}) (M : Mod W) --(B : BarsProps W) --
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K)
       where

open import worldDef(W)
open import progressDef(W)(C)(K)(P)
open import bar(W)
open import barOpen(W)
open import barKripke(W)
open import barBeth(W)(C)(K)(P)



sub-space : (b1 b2 : Bars) → Set(lsuc L)
sub-space b1 b2 =
  (w : 𝕎·) (o : Br)
  → b1 w o
  → b2 w o


-- compared to sub-space, we assume here a bar (in particular monotone)
-- because it is not the case that a space contains only bars
sub-bar : (b1 b2 : Bars) → Set(lsuc L)
sub-bar b1 b2 =
  (w : 𝕎·) (b : 𝔹 b1 w)
  → b2 w (𝔹.bar b)


sub-space→sub-bar : {b1 b2 : Bars} → sub-space b1 b2 → sub-bar b1 b2
sub-space→sub-bar {b1} {b2} h w b = h w (𝔹.bar b) (𝔹.bars b)


kripke-sub-beth : sub-space K𝔹bars IS𝔹bars
kripke-sub-beth w o i c = mkBarredChain w (lower (i w (⊑-refl· _))) 0 (chain.init (pchain.c c))


extPChain : {w w1 : 𝕎·} (e : w ⊑· w1) → pchain w1 → pchain w
extPChain {w} {w1} e c = truncatePChain {w1} {c} {0} {w} (⊑-trans· e (chain.init (pchain.c c)))


pchainThrough : {w w1 : 𝕎·} (e : w ⊑· w1) → pchain w
pchainThrough {w} {w1} e = extPChain e (𝕎→pchain w1)


pchainThrough-prop : {w w1 : 𝕎·} (e : w ⊑· w1) (n : ℕ)
                     → w1 ⊑· chain.seq (pchain.c (pchainThrough e)) n
pchainThrough-prop {w} {w1} e n rewrite +0 n = chain⊑n {w1} n (𝕎→chain· w1)


-- we prove here sub-bar and not sub-spcace because we need the opens of IS𝔹bars to be monotonmic
-- which is not true
beth-sub-open : sub-bar IS𝔹bars O𝔹bars
beth-sub-open w b w1 e1 =
  w2 ,
  e ,
  lift ow2 --lift (BarredChain.b b)
  where
    -- We need a chain that goes through w1:
    c : pchain w
    c = pchainThrough e1

    bc : BarredChain (𝔹.bar b) (pchain.c c)
    bc = 𝔹.bars b c

    n : ℕ
    n = BarredChain.n bc

    w2 : 𝕎·
    w2 = chain.seq (pchain.c c) n

    e : w1 ⊑· w2
    e = pchainThrough-prop e1 n

    e2 : BarredChain.w' bc ⊑· w2
    e2 = BarredChain.ext bc

    ow1 : 𝔹.bar b (BarredChain.w' bc)
    ow1 = BarredChain.b bc

    ow2 : 𝔹.bar b w2
    ow2 = 𝔹.mon b e2 ow1

\end{code}
