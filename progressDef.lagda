\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties


open import util
open import calculus
open import world
open import choice
open import compatible
open import progress

module progressDef {L : Level} (W : PossibleWorlds {L})
                   (C : Choice) (M : Compatible {L} W C) (P : Progress {L} W C M)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)


open Progress


progress· : (c : Name) (w1 w2 : 𝕎·) → Set(L)
progress· = progress P


𝕎→chain· : (w : 𝕎·) → chain w
𝕎→chain· = 𝕎→chain P


progressing : {w : 𝕎·} (c : chain w) → Set(1ℓ ⊔ L)
progressing {w} c =
  (x : Name) (n : ℕ) {r : Res{0ℓ}}
  → compatible· x (chain.seq c n) r
  → Σ ℕ (λ m → n < m × progress· x (chain.seq c n) (chain.seq c m))


chainProgress· : (w : 𝕎·) → progressing (𝕎→chain· w)
chainProgress· = chainProgress P



-- Progressing chain
record pchain (w : 𝕎·) : Set(lsuc(L)) where
  constructor mkPChain
  field
    c : chain w
    p : progressing c



𝕎→pchain : (w : 𝕎·) → pchain w
𝕎→pchain w = mkPChain (𝕎→chain· w) (chainProgress· w)





≤+∸ : (m : ℕ) (n : ℕ) → m ≤ (m + n) ∸ n
≤+∸ m n rewrite +-∸-assoc m {n} {n} ≤-refl | m≤n⇒m∸n≡0 {n} {n} ≤-refl | +-identityʳ m = ≤-refl



<→∸ : {n m k : ℕ} → k ≤ n → n < m → n ∸ k < m ∸ k
<→∸ {n} {m} {0} a b = b
<→∸ {suc n} {suc m} {suc k} a b = <→∸ (s≤s-inj a) (s≤s-inj b)



truncateChain : {w : 𝕎·} {c : chain w} {n : ℕ} {w' : 𝕎·} (e : w' ⊑· chain.seq c n) → chain w'
truncateChain {w} {c} {n} {w'} e = mkChain s e p --q
  where
    s : ℕ → 𝕎·
    s x = chain.seq c (x + n)

    p : (x : ℕ) → s x ⊑· s (suc x)
    p x = chain.prop c (x + n)


truncatePChain : {w : 𝕎·} {c : pchain w} {n : ℕ} {w' : 𝕎·} (e : w' ⊑· chain.seq (pchain.c c) n) → pchain w'
truncatePChain {w} {mkPChain c p} {n} {w'} e = mkPChain c' p'
  where
    c' : chain w'
    c' = truncateChain {w} {c} {n} {w'} e

    p' : progressing (truncateChain {w} {c} {n} {w'} e)
    p' name k {r} comp =
      fst (p name (k + n) comp) ∸ n ,
      <-transʳ (≤+∸ k n) (<→∸ (≤-stepsˡ k ≤-refl) (fst (snd (p name (k + n) comp)))) ,
      q'
      where
         z : n ≤ fst (p name (k + n) comp)
         z = ≤-trans (≤-stepsˡ k ≤-refl) (<⇒≤ (fst (snd (p name (k + n) comp))))

         q' : progress· name ((chain.seq c') k) (chain.seq c' (fst (p name (k + n) comp) ∸ n))
         q' rewrite m∸n+n≡m {fst (p name (k + n) comp)} {n} z = snd (snd (p name (k + n) comp))


chain⊑ : {w w' : 𝕎·} (e : w ⊑· w') → chain w' → chain w
chain⊑ {w} {w'} e (mkChain seq init prop) = mkChain seq (⊑-trans· e init) prop


pchain⊑ : {w w' : 𝕎·} (e : w ⊑· w') → pchain w' → pchain w
pchain⊑ {w} {w'} e (mkPChain c p) = mkPChain (chain⊑ e c) p
