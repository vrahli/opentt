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


module choiceBarInstanceCS (E : Extensionality 0ℓ 3ℓ)
       where


open import worldInstanceCS
open import choiceDef{1ℓ}(choiceCS)
open import worldDef(PossibleWorldsCS)
open import getChoiceDef(PossibleWorldsCS)(choiceCS)(getChoiceCS)
open import newChoiceDef(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)
open import freezeDef(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)
open import progressDef(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)

open import bar(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)
open import barI(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)
open import computation(PossibleWorldsCS)(choiceCS)(getChoiceCS)

open import theory(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)(E)
open import props1(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)(E)
open import props2(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)(E)
open import props3(PossibleWorldsCS)(choiceCS)(getChoiceCS)(newChoiceCS)(freezeCS)(progressCS)(E)



progressing→ΣgetCs≤ : {w : 𝕎·} {c : chain w} {r : Res} (n : Name) (m : ℕ)
                       → compatible· n w r
                       → progressing {w} c
                       → Σ ℕ (λ k → Σ (List ℂ·) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l r) × m < length l))
progressing→ΣgetCs≤ {w} {c} {r} n 0 comp prog = k , (fst i2 ++ fst i3) , fst (snd i3) , len
  where
    z : Σ ℕ (λ m → 0 < m × progress· n (chain.seq c 0) (chain.seq c m))
    z = prog n 0 (⊑-compatible· (chain.init c) comp)

    k : ℕ
    k = fst z

    ltk : 0 < k
    ltk = fst (snd z)

    i1 : Σ (List ℂ·) (λ l → ∈world (mkcs n l r) w × resSatCs 0 l r)
    i1 = comp

    i2 : Σ (List ℂ·) (λ l → ∈world (mkcs n l r) (chain.seq c 0) × resSatCs 0 l r)
    i2 = ⊑-compatible· (chain.init c) comp

    i3 : Σ (List ℂ·) (λ l → ∈world (mkcs n (fst i2 ++ l) r) (chain.seq c k) × 0 < length l)
    i3 = snd (snd z) (fst i2) r (fst (snd i2))

    len : 0 < length (proj₁ i2 ++ proj₁ i3)
    len rewrite length-++ (fst i2) {fst i3} = <-transˡ (snd (snd i3)) (m≤n+m _ _)
progressing→ΣgetCs≤ {w} {c} {r} n (suc m) comp prog = k' , l ++ fst i1 , (fst (snd i1)) , len'
  where
    ind : Σ ℕ (λ k → Σ (List ℂ·) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l r) × m < length l))
    ind = progressing→ΣgetCs≤ {w} {c} n m comp prog

    k : ℕ
    k = fst ind

    l : List ℂ·
    l = fst (snd ind)

    g : getCs n (chain.seq c k) ≡ just (mkcs n l r)
    g = fst (snd (snd ind))

    len : m < length l
    len = snd (snd (snd ind))

    p : Σ ℕ (λ m → k < m × progress· n (chain.seq c k) (chain.seq c m))
    p = prog n k (⊑-compatible· (chain⊑n k c) comp)

    k' : ℕ
    k' = fst p

    ltk' : k < k'
    ltk' = fst (snd p)

    i1 : Σ (List ℂ·) (λ l' → ∈world (mkcs n (l ++ l') r) (chain.seq c k') × 0 < length l')
    i1 = snd (snd p) l r g

    len' : suc m < length (l ++ proj₁ i1)
    len' rewrite length-++ l {fst i1} | suc-+1 m = <-transˡ (+-monoˡ-< 1 len) (+-monoʳ-≤ (length l) (snd (snd i1)))



IS𝔹-ℕ : (w : 𝕎·) (r : Res) (n : Name) (m : ℕ) (comp : compatible· n w r) → IS𝔹 w
IS𝔹-ℕ w r n m comp =
  mk𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set₁
    bar w' = w ⊑· w' × Σ (List ℂ·) (λ l → getCs n w' ≡ just (mkcs n l r) × m < length l)

    bars : (c : pchain w) → BarredChain bar (pchain.c c)
    bars (mkPChain c p) = mkBarredChain (chain.seq c (fst z)) b (fst z) (⊑-refl· _)
      where
        z : Σ ℕ (λ k → Σ (List ℂ·) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l r) × m < length l))
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




{--
⊑-∈world→≤length : {w1 w2 : 𝕎·} {name : Name} {l1 l2 : List ℂ·} {r : Res}
                    → w1 ⊑· w2
                    → ∈world (mkcs name l1 r) w1
                    → ∈world (mkcs name l2 r) w2
                    → length l1 ≤ length l2
⊑-∈world→≤length {w1} {w2} {name} {l1} {l2} {r} e i1 i2
  rewrite fst (snd (≽-pres-∈world e i1))
        | sym (mkcs-inj2 (just-inj i2))
        | length-++ l1 {fst (≽-pres-∈world e i1)}
  = m≤m+n (length l1) (length (fst (≽-pres-∈world e i1)))
--}



⊑-∈world→Σ++ : {w1 w2 : 𝕎·} {name : Name} {l1 l2 : List ℂ·} {r : Res}
                    → w1 ⊑· w2
                    → ∈world (mkcs name l1 r) w1
                    → ∈world (mkcs name l2 r) w2
                    → Σ (List ℂ·) (λ l → l2 ≡ l1 ++ l)
⊑-∈world→Σ++ {w1} {w2} {name} {l1} {l2} {r} e i1 i2
  rewrite fst (snd (≽-pres-∈world e i1))
        | sym (mkcs-inj2 (just-inj i2))
  = fst (≽-pres-∈world e i1) , refl


{--
resSatCs-select→ : {n m : ℕ} {l : List ℂ·} {r : Res} {t : ℂ·}
                    → resSatCs n l r
                    → select m l ≡ just t
                    → ·ᵣ r (m + n) t
resSatCs-select→ {n} {0} {x ∷ l} {r} {t} (c , s) e rewrite just-inj e = c
resSatCs-select→ {n} {suc m} {x ∷ l} {r} {t} (c , s) e rewrite sym (+-suc m n) = resSatCs-select→ s e
--}


→getCsFreezeSeq-replicate : {c : Name} {w : 𝕎·} {l : List ℂ·} {r : Res} {rs : List NRes} (n : ℕ)
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



getCsChoice-freezeSeq→⊎ : {k : ℕ} {c : Name} {r : Res} {l : List NRes} {w : 𝕎·} {t : ℂ·} {n : ℕ}
                           → mkNRes c r ∈ l
                           → NRes-nodup l
                           → compatible· c w r
                           → getCsChoice k c (freezeSeq l w n) ≡ just t
                           → t ≡ Res.def r ⊎ getCsChoice k c w ≡ just t
getCsChoice-freezeSeq→⊎ {k} {c} {r} {l} {w} {t} {n} i nodp comp gc with getCs⊎ c (freezeSeq l w n)
... | inj₁ (mkcs n1 l1 r1 , p) rewrite p | fst (snd comp) = z4 z3
  where
    ts : List ℂ·
    ts = fst comp

    z1 : Σ ℕ (λ k → getCs c (freezeSeq l w n) ≡ just (mkcs c (ts ++ replicate k (Res.def r)) r))
    z1 = →getCsFreezeSeq-replicate n i nodp (fst (snd comp))

    z2 : select k (ts ++ replicate (fst z1) (Res.def r)) ≡ just t
    z2 rewrite snd z1 | sym (mkcs-inj2 (just-inj p)) = gc

    z3 : select k ts ≡ just t ⊎ t ∈ (replicate (fst z1) (Res.def r))
    z3 = select++→⊎∈ {0ℓ} {ℂ·} {k} {ts} z2

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


getCs→≡Name : {w : 𝕎·} {n1 n2 : Name} {l : List ℂ·} {r : Res{0ℓ}}
               → getCs n1 w ≡ just (mkcs n2 l r)
               → n2 ≡ n1
getCs→≡Name {start name res ∷ w} {n1} {n2} {l} {r} e with n1 ≟ name
... | yes p = sym (mkcs-inj1 (just-inj e))
... | no p = getCs→≡Name {w} e
getCs→≡Name {choice name t ∷ w} {n1} {n2} {l} {r} e = getCs→≡Name {w} e


getCs→≡Name-getCs : {w : 𝕎·} {n1 n2 : Name} {l : List ℂ·} {r : Res{0ℓ}}
                     → getCs n1 w ≡ just (mkcs n2 l r)
                     → getCs n1 w ≡ just (mkcs n1 l r)
getCs→≡Name-getCs {start name res ∷ w} {n1} {n2} {l} {r} e with n1 ≟ name
... | yes p rewrite mkcs-inj2 (just-inj e) | mkcs-inj3 (just-inj e) = refl
... | no p = getCs→≡Name-getCs {w} e
getCs→≡Name-getCs {choice name t ∷ w} {n1} {n2} {l} {r} e = getCs→≡Name-getCs {w} e



⊑-isOnlyChoice∈𝕎 : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} {u : ℂ·}
                    → w1 ⊑· w2
                    → isOnlyChoice∈𝕎 u c w2
                    → isOnlyChoice∈𝕎 u c w1
⊑-isOnlyChoice∈𝕎 {c} {w1} {w2} {r} {u} e iso k t z with getCs⊎ c w1
... | inj₁ (mkcs m l r' , p) rewrite p | fst (snd (≽-pres-getCs e (getCs→≡Name-getCs {w1} p))) =
  iso k t (select++-just {0ℓ} {ℂ·} {k} {l} {fst (≽-pres-getCs e (getCs→≡Name-getCs {w1} p))} z)
... | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym z))


{-- xxxxxxxxxxxxxxxxxxxx --}


Typeℂ₀₁-beth-cs : CTerm
Typeℂ₀₁-beth-cs = #QNAT


Typeℂ₀₁-isType-beth-bar : (u : ℕ) (w : 𝕎·) → isType u w Typeℂ₀₁-beth-cs
Typeℂ₀₁-isType-beth-bar u w = eqTypesQNAT


ℂ₀∈Typeℂ₀₁-beth-cs : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-cs Cℂ₀
ℂ₀∈Typeℂ₀₁-beth-cs u w = NUM-equalInType-QNAT u w 0


ℂ₁∈Typeℂ₀₁-beth-cs : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-cs Cℂ₁
ℂ₁∈Typeℂ₀₁-beth-cs u w = NUM-equalInType-QNAT u w 1


isValueℂ₀-beth-cs : isValue Tℂ₀
isValueℂ₀-beth-cs = tt


isValueℂ₁-beth-cs : isValue Tℂ₁
isValueℂ₁-beth-cs = tt


ℂ₀≠ℂ₁-beth-cs : ¬ Cℂ₀ ≡ Cℂ₁
ℂ₀≠ℂ₁-beth-cs ()


∈Typeℂ₀₁→-beth-cs : (i : ℕ) (w : 𝕎·) (a b : CTerm) → equalInType i w Typeℂ₀₁-beth-cs a b → inbar w (λ w' _ → #weakℂEq w' a b)
∈Typeℂ₀₁→-beth-cs i w a b eqi = Bar.∀𝕎-inBarFunc barI aw (equalInType-QNAT→ i w a b eqi)
  where
    aw : ∀𝕎 w (λ w' e' → #weakMonEq w' a b → #weakℂEq w' a b)
    aw w1 e1 h w2 e2 = lift (#NUM (fst (lower (h w2 e2))) , fst (snd (lower (h w2 e2))) , snd (snd (lower (h w2 e2))))


→∈Typeℂ₀₁-beth-cs : (i : ℕ) {w : 𝕎·} {n : ℕ} {c : Name}
                      → inbar w (λ w' _ → weakℂ₀₁M w' (getT n c))
                      → ∈Type i w Typeℂ₀₁-beth-cs (#APPLY (#CS c) (#NUM n))
→∈Typeℂ₀₁-beth-cs i {w} {n} {c} h =
  →equalInType-QNAT i w (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
                     (Bar.∀𝕎-inBarFunc barI aw h)
  where
    aw : ∀𝕎 w (λ w' e' → weakℂ₀₁M w' (getT n c) → #weakMonEq w' (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n)))
    aw w1 e1 z w2 e2 = lift (x (snd (snd (lower (z w2 e2)))))
      where
        t : Term
        t = fst (lower (z w2 e2))

        g : getT n c w2 ≡ just t
        g = fst (snd (lower (z w2 e2)))

        x : (t ⇓ Tℂ₀ at w2 ⊎ t ⇓ Tℂ₁ at w2)
            → Σ ℕ (λ n₁ → APPLY (CS c) (NUM n) ⇓ NUM n₁ at w2 × APPLY (CS c) (NUM n) ⇓ NUM n₁ at w2)
        x (inj₁ y) = 0 , ⇓-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 n c refl g) y , ⇓-trans (Σ-steps-APPLY-CS 0 (NUM n) t w2 n c refl g) y
        x (inj₂ y) = 1 , ⇓-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 n c refl g) y , ⇓-trans (Σ-steps-APPLY-CS 1 (NUM n) t w2 n c refl g) y


-- We so far didn't rely on a specific bar.
-- Here we do
inbar-choice-beth-cs : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res) → compatible· c w r → inBethBar w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t))))
inbar-choice-beth-cs w c m r comp = IS𝔹-ℕ w r c m comp , j
  where
    j : inIS𝔹 (IS𝔹-ℕ w r c m comp) (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t))))
    j {w'} e (e0 , l , g , len) w1 e1 z w2 e2 = lift (fst sel , g1)
      where
        sel : Σ ℂ· (λ t → select m l ≡ just t)
        sel = Σselect {0ℓ} {ℂ·} {m} {l} len

        comp1 : compatible· c w2 r
        comp1 = ⊑-compatible· (⊑-trans· z e2) comp

        l' : List ℂ·
        l' = fst (⊑-∈world→Σ++ (⊑-trans· e1 e2) g (fst (snd comp1)))

        comp2 : ∈world (mkcs c (l ++ l') r) w2
        comp2 rewrite sym (snd (⊑-∈world→Σ++ (⊑-trans· e1 e2) g (fst (snd comp1)))) = fst (snd comp1)

        g1 : getChoice· m c w2 ≡ just (fst sel)
        g1 rewrite comp2 | select++-just {0ℓ} {ℂ·} {m} {l} {l'} (snd sel) = refl


followChoice-beth-cs : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                       → inBethBar w f
                       → isOnlyChoice∈𝕎 (Res.def r) c w
                       → compatible· c w r
                       → freezable· c w
                       → ∃𝕎 w (λ w1 e1 → isOnlyChoice∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)
followChoice-beth-cs c {w} {f} {r} (bar , i) oc comp fb =
  w' , e , iso , comp' , fb' , z
  where
    pc : pchain w
    pc = 𝕎→pchain w

    bp : BarredChain (𝔹.bar bar) (pchain.c pc)
    bp = 𝔹.bars bar pc

    w' : 𝕎·
    w' = BarredChain.w' bp

    e : w ⊑· w'
    e = 𝔹.ext bar (BarredChain.b bp)

    iso : isOnlyChoice∈𝕎 (Res.def r) c w'
    iso = ⊑-isOnlyChoice∈𝕎 {c} {w'} {chain.seq (pchain.c pc) (BarredChain.n bp)} {r}
                            (BarredChain.ext bp)
                            (→isOnlyChoice∈𝕎-𝕎→pchain {c} {w} {r} (BarredChain.n bp) comp oc)

    comp' : compatible· c w' r
    comp' = ⊑-compatible· e comp

    fb' : freezable· c w'
    fb' = tt

    z : f w' e
    z = i e (BarredChain.b bp) w' (⊑-refl· w') e


\end{code}
