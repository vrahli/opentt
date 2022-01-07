\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred ; _⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Maybe
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties


open import util
open import calculus
open import world
open import choice


module choiceBarInstance where


open import worldInstance
open import worldDef(PossibleWorldsCS)
open import choice(PossibleWorldsCS)
open import choiceDef(PossibleWorldsCS)(csChoice)
open import bar(PossibleWorldsCS)(csChoice)
open import computation(PossibleWorldsCS)(csChoice)



suc-+1 : (n : ℕ) → suc n ≡ n + 1
suc-+1 n rewrite +-suc n 0 | +-identityʳ n = refl


progressing→ΣgetCs≤ : {w : 𝕎·} {c : chain w} (n : Name) (m : ℕ)
                       → compatible· n w Resℕ
                       → progressing {w} c
                       → Σ ℕ (λ k → Σ (List Term) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l Resℕ) × m < length l))
progressing→ΣgetCs≤ {w} {c} n 0 comp prog = k , (fst i2 ++ fst i3) , fst (snd i3) , len
  where
    z : Σ ℕ (λ m → 0 < m × progress· n (chain.seq c 0) (chain.seq c m))
    z = prog n 0 (⊑-compatible· (chain.init c) comp)

    k : ℕ
    k = fst z

    ltk : 0 < k
    ltk = fst (snd z)

    i1 : Σ (List Term) (λ l → ∈world (mkcs n l Resℕ) w)
    i1 = comp

    i2 : Σ (List Term) (λ l → ∈world (mkcs n l Resℕ) (chain.seq c 0))
    i2 = ⊑-compatible· (chain.init c) comp

    i3 : Σ (List Term) (λ l → ∈world (mkcs n (fst i2 ++ l) Resℕ) (chain.seq c k) × 0 < length l)
    i3 = snd (snd z) (fst i2) Resℕ (snd i2)

    len : 0 < length (proj₁ i2 ++ proj₁ i3)
    len rewrite length-++ (fst i2) {fst i3} = <-transˡ (snd (snd i3)) (m≤n+m _ _)
progressing→ΣgetCs≤ {w} {c} n (suc m) comp prog = k' , l ++ fst i1 , (fst (snd i1)) , len'
  where
    ind : Σ ℕ (λ k → Σ (List Term) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l Resℕ) × m < length l))
    ind = progressing→ΣgetCs≤ {w} {c} n m comp prog

    k : ℕ
    k = fst ind

    l : List Term
    l = fst (snd ind)

    g : getCs n (chain.seq c k) ≡ just (mkcs n l Resℕ)
    g = fst (snd (snd ind))

    len : m < length l
    len = snd (snd (snd ind))

    p : Σ ℕ (λ m → k < m × progress· n (chain.seq c k) (chain.seq c m))
    p = prog n k (⊑-compatible· (chain⊑n k c) comp)

    k' : ℕ
    k' = fst p

    ltk' : k < k'
    ltk' = fst (snd p)

    i1 : Σ (List Term) (λ l' → ∈world (mkcs n (l ++ l') Resℕ) (chain.seq c k') × 0 < length l')
    i1 = snd (snd p) l Resℕ g

    len' : suc m < length (l ++ proj₁ i1)
    len' rewrite length-++ l {fst i1} | suc-+1 m = <-transˡ (+-monoˡ-< 1 len) (+-monoʳ-≤ (length l) (snd (snd i1)))



IS𝔹-ℕ : (w : 𝕎·) (n : Name) (m : ℕ) (comp : compatible· n w Resℕ) → IS𝔹 w
IS𝔹-ℕ w n m comp =
  mkIS𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set₁
    bar w' = w ⊑· w' × Σ (List Term) (λ l → getCs n w' ≡ just (mkcs n l Resℕ) × m < length l)

    bars : (c : pchain w) → BarsProp bar (pchain.c c)
    bars (mkPChain c p) = mkBarsProp (chain.seq c (fst z)) b (fst z) (⊑-refl· _)
      where
        z : Σ ℕ (λ k → Σ (List Term) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l Resℕ) × m < length l))
        z = progressing→ΣgetCs≤ {w} {c} n m comp p

        b : bar (chain.seq c (fst z))
        b = chain⊑n (fst z) c , snd z --fst (snd z) , fst (snd (snd z)) , snd (snd (snd z))

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (e , l , g , len) = e

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (e' , l , g , len) = ⊑-trans· e' e , l ++ fst (≽-pres-∈world e g) , snd (≽-pres-∈world e g) , ln
      where
        ln : m < length (l ++ fst (≽-pres-∈world e g))
        ln rewrite length-++ l {fst (≽-pres-∈world e g)} = ≤-stepsʳ (length (fst (≽-pres-∈world e g))) len


Σselect : {L : Level} {A : Set(L)} {k : ℕ} {l : List A}
          → k < length l
          → Σ A (λ t → select k l ≡ just t)
Σselect {L} {A} {0} {x ∷ l} len = x , refl
Σselect {L} {A} {suc k} {x ∷ l} len = Σselect {L} {A} {k} {l} (s≤s-inj len)


choice-weakℕ-beth : (w : 𝕎·) (c : Name) (m : ℕ)
                     → compatible· c w Resℕ
                     → inBethBar w (λ w' _ → weakℕM w' (getChoice· m c))
choice-weakℕ-beth w c m comp = IS𝔹-ℕ w c m comp , i
  where
    i : inIS𝔹 (IS𝔹-ℕ w c m comp) (λ w' _ → weakℕM w' (getChoice· m c))
    i {w'} e (e0 , l , g , len) w1 e1 z w2 e2 = lift (fst t , g2 , {!!})
      where
        g1 : Σ (List Term) (λ l' → getCs c w2 ≡ just (mkcs c (l ++ l') Resℕ))
        g1 = ≽-pres-getCs (⊑-trans· e1 e2) g

        t : Σ Term (λ t → select m l ≡ just t)
        t = Σselect {0ℓ} {Term} {m} {l} len

        g2 : getChoice· m c w2 ≡ just (fst (Σselect {0ℓ} {Term} {m} {l} len))
        g2 rewrite snd g1 | select++-just {0ℓ} {Term} {m} {l} {fst g1} (snd t) = refl


followChoice-beth : (u : Term) (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                    → inBethBar w f
                    → isOnlyChoice∈𝕎 u c w
                    → compatible· c w r
                    → Σ 𝕎· (λ w1 → Σ (w ⊑· w1) (λ e1 → isOnlyChoice∈𝕎 u c w1 × compatible· c w1 r × f w1 e1))
followChoice-beth u c {w} {f} {r} i oc comp = {!!}
\end{code}
