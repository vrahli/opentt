\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
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


module choiceBarInstanceCS where


open import worldInstanceCS
open import worldDef(PossibleWorldsCS)
open import choice(PossibleWorldsCS)
open import choiceDef(PossibleWorldsCS)(csChoice)
open import bar(PossibleWorldsCS)(csChoice)
open import computation(PossibleWorldsCS)(csChoice)



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

    i1 : Σ (List Term) (λ l → ∈world (mkcs n l Resℕ) w × resSatCs 0 l Resℕ)
    i1 = comp

    i2 : Σ (List Term) (λ l → ∈world (mkcs n l Resℕ) (chain.seq c 0) × resSatCs 0 l Resℕ)
    i2 = ⊑-compatible· (chain.init c) comp

    i3 : Σ (List Term) (λ l → ∈world (mkcs n (fst i2 ++ l) Resℕ) (chain.seq c k) × 0 < length l)
    i3 = snd (snd z) (fst i2) Resℕ (fst (snd i2))

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
    mon {w1} {w2} e (e' , l , g , len) = ⊑-trans· e' e , l ++ fst (≽-pres-∈world e g) , fst (snd (≽-pres-∈world e g)) , ln
      where
        ln : m < length (l ++ fst (≽-pres-∈world e g))
        ln rewrite length-++ l {fst (≽-pres-∈world e g)} = ≤-stepsʳ (length (fst (≽-pres-∈world e g))) len




⊑-∈world→≤length : {w1 w2 : 𝕎·} {name : Name} {l1 l2 : List Term} {r : Res}
                    → w1 ⊑· w2
                    → ∈world (mkcs name l1 r) w1
                    → ∈world (mkcs name l2 r) w2
                    → length l1 ≤ length l2
⊑-∈world→≤length {w1} {w2} {name} {l1} {l2} {r} e i1 i2
  rewrite fst (snd (≽-pres-∈world e i1))
        | sym (mkcs-inj2 (just-inj i2))
        | length-++ l1 {fst (≽-pres-∈world e i1)}
  = m≤m+n (length l1) (length (fst (≽-pres-∈world e i1)))



⊑-∈world→Σ++ : {w1 w2 : 𝕎·} {name : Name} {l1 l2 : List Term} {r : Res}
                    → w1 ⊑· w2
                    → ∈world (mkcs name l1 r) w1
                    → ∈world (mkcs name l2 r) w2
                    → Σ (List Term) (λ l → l2 ≡ l1 ++ l)
⊑-∈world→Σ++ {w1} {w2} {name} {l1} {l2} {r} e i1 i2
  rewrite fst (snd (≽-pres-∈world e i1))
        | sym (mkcs-inj2 (just-inj i2))
  = fst (≽-pres-∈world e i1) , refl


resSatCs-select→ : {n m : ℕ} {l : List Term} {r : Res} {t : Term}
                    → resSatCs n l r
                    → select m l ≡ just t
                    → ·ᵣ r (m + n) t
resSatCs-select→ {n} {0} {x ∷ l} {r} {t} (c , s) e rewrite just-inj e = c
resSatCs-select→ {n} {suc m} {x ∷ l} {r} {t} (c , s) e rewrite sym (+-suc m n) = resSatCs-select→ s e



choice-weakℕ-beth : (w : 𝕎·) (c : Name) (m : ℕ)
                     → compatible· c w Resℕ
                     → inBethBar w (λ w' _ → weakℕM w' (getChoice· m c))
choice-weakℕ-beth w c m comp = IS𝔹-ℕ w c m comp , i
  where
    i : inIS𝔹 (IS𝔹-ℕ w c m comp) (λ w' _ → weakℕM w' (getChoice· m c))
    i {w'} e (e0 , l , g , len) w1 e1 z w2 e2 = lift (fst sel , g1 , num)
      where
        comp1 : compatible· c w2 Resℕ
        comp1 = ⊑-compatible· (⊑-trans· z e2) comp

        sel : Σ Term (λ t → select m l ≡ just t)
        sel = Σselect {0ℓ} {Term} {m} {l} len

        l' : List Term
        l' = fst (⊑-∈world→Σ++ (⊑-trans· e1 e2) g (fst (snd comp1)))

        comp2 : ∈world (mkcs c (l ++ l') Resℕ) w2 × resSatCs 0 (l ++ l') Resℕ
        comp2 rewrite sym (snd (⊑-∈world→Σ++ (⊑-trans· e1 e2) g (fst (snd comp1)))) = snd comp1

        sel2 : select m (l ++ l') ≡ just (fst sel)
        sel2 rewrite select++-just {0ℓ} {Term} {m} {l} {l'} (snd sel) = refl

        g1 : getChoice· m c w2 ≡ just (fst sel)
        g1 rewrite (fst comp2) | select++-just {0ℓ} {Term} {m} {l} {l'} (snd sel) = refl

        sat : ·ᵣ Resℕ (m + 0) (fst sel)
        sat = resSatCs-select→ (snd comp2) sel2

        num : Σ ℕ (λ n → fst sel ⇓ NUM n at w2)
        num = fst sat , cn
          where
            cn : fst sel ⇓ NUM (fst sat) at w2
            cn rewrite sym (snd sat) = ⇓-refl _ _




→getCsFreezeSeq-replicate : {c : Name} {w : 𝕎·} {l : List Term} {r : Res} {rs : List NRes} (n : ℕ)
                             → mkNRes c r ∈ rs
                             → NRes-nodup rs
                             → getCs c w ≡ just (mkcs c l r)
                             → Σ ℕ (λ k → getCs c (freezeSeq rs w n) ≡ just (mkcs c (l ++ replicate k (Res.def r)) r))
→getCsFreezeSeq-replicate {c} {w} {l} {r} {rs} 0 i nodp h = 0 , h'
  where
    h' : getCs c w ≡ just (mkcs c (l ++ []) r)
    h' rewrite ++[] l = h
→getCsFreezeSeq-replicate {c} {w} {l} {r} {rs} (suc n) i nodp h = suc (fst ind) , cc
  where
    ind : Σ ℕ (λ k → getCs c (freezeSeq rs w n) ≡ just (mkcs c (l ++ replicate k (Res.def r)) r))
    ind = →getCsFreezeSeq-replicate n i nodp h

    j : mkNRes c (mkRes (Res.res r) (Res.def r) (Res.sat r)) ∈ rs
    j rewrite Resη r = i

    cc : getCs c (freezeList rs (freezeSeq rs w n)) ≡ just (mkcs c (l ++ Res.def r ∷ replicate (fst ind) (Res.def r)) r)
    cc rewrite ∷replicate≡replicate∷ʳ (fst ind) (Res.def r) | sym (++-assoc l (replicate (fst ind) (Res.def r)) [ Res.def r ]) =
      getCs-freezeList≡ nodp j (snd ind)



getCsChoice-freezeSeq→⊎ : {k : ℕ} {c : Name} {r : Res} {l : List NRes} {w : 𝕎·} {t : Term} {n : ℕ}
                           → mkNRes c r ∈ l
                           → NRes-nodup l
                           → compatible· c w r
                           → getCsChoice k c (freezeSeq l w n) ≡ just t
                           → t ≡ Res.def r ⊎ getCsChoice k c w ≡ just t
getCsChoice-freezeSeq→⊎ {k} {c} {r} {l} {w} {t} {n} i nodp comp gc with getCs⊎ c (freezeSeq l w n)
... | inj₁ (mkcs n1 l1 r1 , p) rewrite p | fst (snd comp) = z4 z3
  where
    ts : List Term
    ts = fst comp

    z1 : Σ ℕ (λ k → getCs c (freezeSeq l w n) ≡ just (mkcs c (ts ++ replicate k (Res.def r)) r))
    z1 = →getCsFreezeSeq-replicate n i nodp (fst (snd comp))

    z2 : select k (ts ++ replicate (fst z1) (Res.def r)) ≡ just t
    z2 rewrite snd z1 | sym (mkcs-inj2 (just-inj p)) = gc

    z3 : select k ts ≡ just t ⊎ t ∈ (replicate (fst z1) (Res.def r))
    z3 = select++→⊎∈ {0ℓ} {Term} {k} {ts} z2

    z4 : (select k ts ≡ just t ⊎ t ∈ (replicate (fst z1) (Res.def r))) → (t ≡ Res.def r ⊎ select k (proj₁ comp) ≡ just t)
    z4 (inj₁ x) = inj₂ x
    z4 (inj₂ y) = inj₁ (∈replicate→ y)

... | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym gc))


→isOnlyChoice∈𝕎-𝕎→pchain : {c : Name} {w : 𝕎·} {r : Res{0ℓ}} (n : ℕ)
                              → compatible· c w r
                              → isOnlyChoice∈𝕎 (Res.def r) c w
                              → isOnlyChoice∈𝕎 (Res.def r) c (𝕎→seq w n)
→isOnlyChoice∈𝕎-𝕎→pchain {c} {w} {r} n comp iso k t e = concl u
  where
    i : mkNRes c r ∈ wrdom w
    i = getCs→mkNRes∈wrdom {c} {w} (fst (snd comp))

    u : t ≡ Res.def r ⊎ getCsChoice k c w ≡ just t
    u = getCsChoice-freezeSeq→⊎ {k} {c} {r} {wrdom w} {w} {t} {n} i (NRes-nodup-wdom w) comp e

    concl : (t ≡ Res.def r ⊎ getCsChoice k c w ≡ just t) → t ≡ Res.def r
    concl (inj₁ x) = x
    concl (inj₂ y) = iso k t y


getCs→≡Name : {w : 𝕎·} {n1 n2 : Name} {l : List Term} {r : Res{0ℓ}}
               → getCs n1 w ≡ just (mkcs n2 l r)
               → n2 ≡ n1
getCs→≡Name {start name res ∷ w} {n1} {n2} {l} {r} e with n1 ≟ name
... | yes p = sym (mkcs-inj1 (just-inj e))
... | no p = getCs→≡Name {w} e
getCs→≡Name {choice name t ∷ w} {n1} {n2} {l} {r} e = getCs→≡Name {w} e


getCs→≡Name-getCs : {w : 𝕎·} {n1 n2 : Name} {l : List Term} {r : Res{0ℓ}}
                     → getCs n1 w ≡ just (mkcs n2 l r)
                     → getCs n1 w ≡ just (mkcs n1 l r)
getCs→≡Name-getCs {start name res ∷ w} {n1} {n2} {l} {r} e with n1 ≟ name
... | yes p rewrite mkcs-inj2 (just-inj e) | mkcs-inj3 (just-inj e) = refl
... | no p = getCs→≡Name-getCs {w} e
getCs→≡Name-getCs {choice name t ∷ w} {n1} {n2} {l} {r} e = getCs→≡Name-getCs {w} e



⊑-isOnlyChoice∈𝕎 : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} {u : Term}
                    → w1 ⊑· w2
                    → isOnlyChoice∈𝕎 u c w2
                    → isOnlyChoice∈𝕎 u c w1
⊑-isOnlyChoice∈𝕎 {c} {w1} {w2} {r} {u} e iso k t z with getCs⊎ c w1
... | inj₁ (mkcs m l r' , p) rewrite p | fst (snd (≽-pres-getCs e (getCs→≡Name-getCs {w1} p))) =
  iso k t (select++-just {0ℓ} {Term} {k} {l} {fst (≽-pres-getCs e (getCs→≡Name-getCs {w1} p))} z)
... | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym z))



followChoice-beth : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                    → inBethBar w f
                    → isOnlyChoice∈𝕎 (Res.def r) c w
                    → compatible· c w r
                    → freezable· c w
                    → Σ 𝕎· (λ w1 → Σ (w ⊑· w1) (λ e1 → isOnlyChoice∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1))
followChoice-beth c {w} {f} {r} (bar , i) oc comp fb =
  w' , e , iso , comp' , fb' , z
  where
    pc : pchain w
    pc = 𝕎→pchain w

    bp : BarsProp (IS𝔹.bar bar) (pchain.c pc)
    bp = IS𝔹.bars bar pc

    w' : 𝕎·
    w' = BarsProp.w' bp

    e : w ⊑· w'
    e = IS𝔹.ext bar (BarsProp.b bp)

    iso : isOnlyChoice∈𝕎 (Res.def r) c w'
    iso = ⊑-isOnlyChoice∈𝕎 {c} {w'} {chain.seq (pchain.c pc) (BarsProp.n bp)} {r}
                            (BarsProp.ext bp)
                            (→isOnlyChoice∈𝕎-𝕎→pchain {c} {w} {r} (BarsProp.n bp) comp oc)

    comp' : compatible· c w' r
    comp' = ⊑-compatible· e comp

    fb' : freezable· c w'
    fb' = tt

    z : f w' e
    z = i e (BarsProp.b bp) w' (⊑-refl· w') e


\end{code}
