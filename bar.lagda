\begin{code}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)

open import world
-- get rid of worldInstance here and only use world
-- make it a parameter of bar
--open import worldInstance


module bar (W : PossibleWorlds) where
open import worldDef(W)


record Bar : Set₂ where
  constructor mkBar
  field
    -- Operators
    inBar             : (w : 𝕎·) (f : wPred w) → Set₁
    inBar'            : (w : 𝕎·) {g : wPred w} (h : inBar w g) (f : wPredDep g) → Set₁
    ↑inBar            : {w : 𝕎·} {f : wPred w} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBar w' (↑wPred f e)
    ↑'inBar           : {w : 𝕎·} {f : wPred w} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBar w' (↑wPred' f e)
    atBar             : {w : 𝕎·} {f : wPred w} (i : inBar w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set₁
    -- Axioms
    inBarFunc         : {w : 𝕎·} {f g : wPred w}
                        → inBar w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    ∀𝕎-inBarFunc    : {w : 𝕎·} {f g : wPred w}
                        → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    inBar-inBar'      : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                        → inBar w (λ w' e' → (x : f w' e') → g w' e' x)
                        → (i : inBar w f) → inBar' w i g
    ∀𝕎-inBar-inBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') (at : atBar i w' e' x) → g w' e' x)
                        → inBar' w i g
    ∀𝕎-inBar        : {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → inBar w f
    inBar-idem        : {w : 𝕎·} {f : wPred w}
                        → inBar w (λ w' e' → inBar w' (↑wPred' f e'))
                        → inBar w f
    inBar'-idem       : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → inBar w (λ w' e' → inBar' w' (↑'inBar i e') (↑wPredDep' g e'))
                        → inBar' w i g
    ∀𝕎-inBar'-inBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inBar w f)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') → atBar i w' e' x → g w' e' x → h w' e')
                        → inBar' w i g → inBar w h
    inBar'-comb       : {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : inBar w f)
                        → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                                           → g w' e' zg → h w' e' zh → k w' e' z)
                        → inBar' w i g → inBar' w i h → inBar' w i k
    inBar'-change    : {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k} (i : inBar w f) (j : inBar w k)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e') → atBar i w' e' x → atBar j w' e' y
                                           → g w' e' x → h w' e' y)
                        → inBar' w i g → inBar' w j h
    inBar-const       : {w : 𝕎·} {t : Set₁} → inBar w (λ w e → t) → t

--    wPredDepExtIrrBar : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : inBar w f) → Set₁
{--    ↑inBar'           : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f) {w' : 𝕎·} (e : w' ⊇ w)
                        → inBar' w i g → inBar' w' (↑inBar i e) (↑wPredDep g e)--}
--    atBar             : {w : 𝕎·} {f : wPred w} (i : inBar w f) (w' : 𝕎·) → Set₁
{--    ↑inBar'           : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f) {w' : 𝕎·} (e : w' ⊇ w) {h : wPredDep (↑wPred f e)}
                        → ∀𝕎 w' (λ w'' e'' → (x y : f w'' (⊑-trans· e e'')) (at : atBar i w'' (⊑-trans· e e'') x) → g w'' (⊑-trans· e e'') x → h w'' e'' y)
                        → inBar' w i g → inBar' w' (↑inBar i e) h--}

{--    inBar'-inBar'      : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPredDep f} (i : inBar w f)
                         → wPredDepExtIrrBar g i
                         → wPredDepExtIrrBar h i
                         → inBar' w i (λ w' e' z → g w' e' z → h w' e' z)
                         → inBar' w i g → inBar' w i h--}

{--    inBar-mon         : {w2 w1 : 𝕎·} {f : wPred w1} (e : w2 ⊇ w1)
                        → inBar w1 f → inBar w2 (↑wPred f e)
    inBar'-mon        : {w2 w1 : 𝕎·} {f : wPred w1} {g : wPredDep f} (e : w2 ⊇ w1) (i : inBar w1 f)
                        → inBar' w1 i g → inBar' w2 (inBar-mon e i) (↑wPredDep' g e)--}

{--    inBar-idem2       : {w : 𝕎·} {f : wPred w}
                        → wPredExtIrr f
                        → inBar w (λ w' e' → inBar w' (↑wPred f e'))
                        → inBar w f--}
{--    inBar'-idem2      : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → wPredDepExtIrrBar g i
                        → inBar w (λ w' e' → inBar' w' (↑inBar i e') (↑wPredDep g e'))
                        → inBar' w i g--}
{--    ∀𝕎-inBar'-inBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w}
                        → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                        → (i : inBar w f) → inBar' w i g → inBar w h--}
{--    inBar'-change     : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i j : inBar w f)
                        → ∀𝕎 w (λ w' e' → (x y : f w' e') → atBar i w' e' x → atBar j w' e' y → g w' e' x → g w' e' y)
                        → inBar' w i g → inBar' w j g--}
    -- a more general version


-- This is a consequence of [∀𝕎-inBar'-inBar]
inBar'-inBar : (b : Bar) {w : 𝕎·} {f : wPred w} {h : wPred w}
               → (i : Bar.inBar b w f) → Bar.inBar' b w i (λ w1 e1 z → h w1 e1) → Bar.inBar b w h
inBar'-inBar b {w} {f} {h} i q = Bar.∀𝕎-inBar'-inBar b i (λ w1 e1 x at z → z) q


-- This is a consequence of [inBar'-comb] for 3 dependent bars
inBar'3 : (b : Bar) {w : 𝕎·} {f : wPred w} {g h k j : wPredDep f} (i : Bar.inBar b w f)
          → ∀𝕎 w (λ w' e' → (z : f w' e') (zg : f w' e') (zh : f w' e') (zk : f w' e')
                             → g w' e' zg → h w' e' zh → k w' e' zk → j w' e' z)
          → Bar.inBar' b w i g → Bar.inBar' b w i h → Bar.inBar' b w i k → Bar.inBar' b w i j
inBar'3 b {w} {f} {g} {h} {k} {j} i imp ig ih ik = c
  where
    ip : Bar.inBar' b w i (λ w1 e1 z → Σ (f w1 e1) λ zg → Σ (f w1 e1) λ zh → g w1 e1 zg × h w1 e1 zh)
    ip = Bar.inBar'-comb b i (λ w1 e1 z zg zh xg xh → zg , zh , xg , xh) ig ih

    c : Bar.inBar' b w i j
    c = Bar.inBar'-comb b i (λ w1 e1 zj zh zk (zg' , zh' , ig , ih) ik → imp w1 e1 zj zg' zh' zk ig ih ik) ip ik


-- f holds in an open bar
inOpenBar : (w : 𝕎·) (f : wPred w) → Set₁
inOpenBar w f =
  ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → ∀𝕎 w2 (λ w3 e3 →
     (z : w ⊑· w3) → f w3 z)))


-- f holds in an open bar that depends on another open bar h
inOpenBar' : (w : 𝕎·) {g : wPred w} (h : inOpenBar w g) (f : wPredDep g) → Set₁
inOpenBar' w h f =
  ∀𝕎 w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           ∃∀𝕎 w1 (λ w2 e2 → (z : w ⊑· w2) → f w2 z (q w2 e2 z)))


wPredDepExtIrr-inOpenBar : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : inOpenBar w f) → Set₁
wPredDepExtIrr-inOpenBar {w} {f} h i =
  (w0 w1 w2 : 𝕎·) (e0 : w ⊑· w0) (e1 : w ⊑· w1) (e2 : w ⊑· w2)
  (e0' : fst (i w0 e0) ⊑· w2) (e1' : fst (i w1 e1) ⊑· w2) (e2' : w ⊑· w2)
  → h w2 e2' (snd (snd (i w0 e0)) w2 e0' e2')
  → h w2 e2 (snd (snd (i w1 e1)) w2 e1' e2)


inOpenBarFunc : {w : 𝕎·} {f g : wPred w} → inOpenBar w (λ w' e' → f w' e' → g w' e') → inOpenBar w f → inOpenBar w g
inOpenBarFunc {w} {f} {g} F h w1 e1 =
  fst h2 , ⊑-trans· e2 (fst (snd h2)) , h3
  where
    h1 : ∃∀𝕎 w1 λ w2 e2 → (z : w ⊑· w2) → f w2 z
    h1 = h w1 e1

    w2 : 𝕎·
    w2 = fst h1

    e2 : w1 ⊑· w2
    e2 = fst (snd h1)

    h2 : ∃∀𝕎 w2 (λ w' e' → (z : w ⊑· w') → f w' z → g w' z)
    h2 = F w2 (⊑-trans· e1 e2)

    w3 : 𝕎·
    w3 = fst h2

    e3 : w2 ⊑· w3
    e3 = fst (snd h2)

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w ⊑· w4) → g w4 z)
    h3 w4 e4 z = snd (snd h2) w4 e4 z (snd (snd h1) w4 (⊑-trans· e3 e4) z)


∀𝕎-inOpenBarFunc : {w : 𝕎·} {f g : wPred w} → ∀𝕎 w (λ w' e' → f w' e' → g w' e') → inOpenBar w f → inOpenBar w g
∀𝕎-inOpenBarFunc {w} {f} {g} F h w1 e1 =
  w2 , e2 , h3
  where
    h1 : ∃∀𝕎 w1 λ w2 e2 → (z : w ⊑· w2) → f w2 z
    h1 = h w1 e1

    w2 : 𝕎·
    w2 = fst h1

    e2 : w1 ⊑· w2
    e2 = fst (snd h1)

    h2 : ∀𝕎 w2 λ w3 e3 → (z : w ⊑· w3) → f w3 z
    h2 = snd (snd h1)

    h3 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → g w3 z)
    h3 w3 e3 z = F w3 z (h2 w3 e3 z)


inOpenBar-inOpenBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                       → inOpenBar w (λ w' e' → (x : f w' e') → g w' e' x)
                       → (i : inOpenBar w f) → inOpenBar' w i g
inOpenBar-inOpenBar' {w} {f} {g} h i w1 e1 = w3 , e3 , h3
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h0 = snd (snd (i w1 e1))

    h1 : ∃∀𝕎 w2 (λ w' e' → (z : w ⊑· w') (x : f w' z) → g w' z x)
    h1 = h w2 (⊑-trans· e1 e2)

    w3 : 𝕎·
    w3 = fst h1

    e3 : w2 ⊑· w3
    e3 = fst (snd h1)

    h2 : ∀𝕎 w3 (λ w' e' → (z : w ⊑· w') (x : f w' z) → g w' z x)
    h2 = snd (snd h1)

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w ⊑· w4) → g w4 z (h0 w4 (⊑-trans· e3 e4) z))
    h3 w4 e4 z = h2 w4 e4 z (h0 w4 (⊑-trans· e3 e4) z)



inOpenBar'-inOpenBar' : {w : 𝕎·} {f : wPred w} {g h : wPredDep f} (i : inOpenBar w f)
                        → wPredDepExtIrr-inOpenBar g i
                        → wPredDepExtIrr-inOpenBar h i
                        → inOpenBar' w i (λ w' e' z → g w' e' z → h w' e' z)
                        → inOpenBar' w i g → inOpenBar' w i h
inOpenBar'-inOpenBar' {w} {f} {g} {h} i irrg irrh j o w1 e1 =
  w5 ,
  ⊑-trans· (⊑-trans· e3 e4) e5 ,
  λ w6 e6 z →
    irrh
      w3 w1 w6
      (⊑-trans· (⊑-trans· e1 e2) e3) e1 z
      (⊑-trans· e5 e6)
      (⊑-trans· (⊑-trans· (⊑-trans· e3 e4) e5) e6)
      z
      (h5 w6 e6 z (irrg
                     w1 w3 w6
                     e1 (⊑-trans· (⊑-trans· e1 e2) e3) z
                     (⊑-trans· e3 (⊑-trans· (⊑-trans· e4 e5) e6))
                     (⊑-trans· e5 e6)
                     z
                     (h3 w6 (⊑-trans· (⊑-trans· e4 e5) e6) z)))
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h2 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h2 = snd (snd (i w1 e1))

    w3 : 𝕎·
    w3 = fst (o w1 e1)

    e3 : w2 ⊑· w3
    e3 = fst (snd (o w1 e1))

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w ⊑· w4) → g w4 z (h2 w4 (⊑-trans· e3 e4) z))
    h3 = snd (snd (o w1 e1))

    w4 : 𝕎·
    w4 = fst (i w3 (⊑-trans· (⊑-trans· e1 e2) e3))

    e4 : w3 ⊑· w4
    e4 = fst (snd (i w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    h4 : ∀𝕎 w4 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h4 = snd (snd (i w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    w5 : 𝕎·
    w5 = fst (j w3 (⊑-trans· (⊑-trans· e1 e2) e3))

    e5 : w4 ⊑· w5
    e5 = fst (snd (j w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    h5 : ∀𝕎 w5 (λ w6 e6 → (z : w ⊑· w6) → g w6 z (h4 w6 (⊑-trans· e5 e6) z) → h w6 z (h4 w6 (⊑-trans· e5 e6) z))
    h5 = snd (snd (j w3 (⊑-trans· (⊑-trans· e1 e2) e3)))



↑inOpenBar : {w1 : 𝕎·} {f : wPred w1} (i : inOpenBar w1 f) {w2 : 𝕎·} (e : w1 ⊑· w2) → inOpenBar w2 (↑wPred f e)
↑inOpenBar {w1} {f} i {w2} e w' e' = w0 , e0 , h0
  where
    w0 : 𝕎·
    w0 = fst (i w' (⊑-trans· e e'))

    e0 : w' ⊑· w0
    e0 = fst (snd (i w' (⊑-trans· e e')))

    h0 : ∀𝕎 w0 (λ w3 e3 → (z : w2 ⊑· w3) → ↑wPred f e w3 z)
    h0 w3 e3 z = snd (snd (i w' (⊑-trans· e e'))) w3 e3 (⊑-trans· e z)



↑'inOpenBar : {w1 : 𝕎·} {f : wPred w1} (i : inOpenBar w1 f) {w2 : 𝕎·} (e : w1 ⊑· w2) → inOpenBar w2 (↑wPred' f e)
↑'inOpenBar {w1} {f} i {w2} e w' e' = w0 , e0 , h0
  where
    w0 : 𝕎·
    w0 = fst (i w' (⊑-trans· e e'))

    e0 : w' ⊑· w0
    e0 = fst (snd (i w' (⊑-trans· e e')))

    h0 : ∀𝕎 w0 (λ w3 e3 → (z : w2 ⊑· w3) → ↑wPred' f e w3 z)
    h0 w3 e3 z x = snd (snd (i w' (⊑-trans· e e'))) w3 e3 x



↑inOpenBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f) {w' : 𝕎·} (e : w ⊑· w')
              → inOpenBar' w i g → inOpenBar' w' (↑inOpenBar i e) (↑wPredDep g e)
↑inOpenBar' {w} {f} {g} i {w'} e j w1 e1 =
  w2 , e2 , h
  where
    w2 : 𝕎·
    w2 = fst (j w1 (⊑-trans· e e1))

    e2 : (fst (↑'inOpenBar i e w1 e1)) ⊑· w2
    e2 = fst (snd (j w1 (⊑-trans· e e1)))

    h : ∀𝕎 w2 (λ w3 e3 → (z : w' ⊑· w3) → ↑wPredDep g e w3 z (snd (snd (↑inOpenBar i e w1 e1)) w3 (⊑-trans· e2 e3) z))
    h w3 e3 z = snd (snd (j w1 (⊑-trans· e e1))) w3 e3 (⊑-trans· e z)




--atOpenBar : {w : 𝕎·} {f : wPred w} (i : inOpenBar w f) (w' : 𝕎·) → Set₁
--atOpenBar {w} {f} i w' = Σ world (λ w1 → Σ (w ⊑· w1) (λ e1 → w' ≽ fst (i w1 e1)))
-- --  Σ (w' ≽ fst (i w1 e1)) (λ e2 → snd (snd (i w1 e1)) w' e2 e)))


data atOpenBar {w : 𝕎·} {f : wPred w} (i : inOpenBar w f) : (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set₁
data atOpenBar {w} {f} i where
  ATOPENBAR : (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : fst (i w1 e1) ⊑· w2) (z : w ⊑· w2)
              → atOpenBar {w} {f} i w2 z (snd (snd (i w1 e1)) w2 e2 z)




↑inOpenBar'' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f) {w' : 𝕎·} (e : w ⊑· w') {h : wPredDep (↑wPred f e)}
               → ∀𝕎 w' (λ w'' e'' → (x y : f w'' (⊑-trans· e e'')) (at : atOpenBar i w'' (⊑-trans· e e'') x) → g w'' (⊑-trans· e e'') x → h w'' e'' y)
               → inOpenBar' w i g → inOpenBar' w' (↑inOpenBar i e) h
↑inOpenBar'' {w} {f} {g} i {w'} e {h} aw j w1 e1 =
  w2 , e2 , q
  where
    w2 : 𝕎·
    w2 = fst (j w1 (⊑-trans· e e1))

    e2 : (fst (↑'inOpenBar i e w1 e1)) ⊑· w2
    e2 = fst (snd (j w1 (⊑-trans· e e1)))

    q : ∀𝕎 w2 (λ w3 e3 → (z : w' ⊑· w3) → h w3 z (snd (snd (↑inOpenBar i e w1 e1)) w3 (⊑-trans· e2 e3) z))
    q w3 e3 z = aw w3 z ((snd (snd (i w1 (⊑-trans· e e1))) w3 (⊑-trans· e2 e3) (⊑-trans· e z)))
                   (snd (snd (↑inOpenBar i e w1 e1)) w3 (⊑-trans· e2 e3) z)
                   (ATOPENBAR w1 (⊑-trans· e e1) w3 (⊑-trans· (proj₁ (snd (j w1 (⊑-trans· e e1)))) e3) (⊑-trans· e z))
                   (snd (snd (j w1 (⊑-trans· e e1))) w3 e3 (⊑-trans· e z))




inOpenBar'-idem : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                  → inOpenBar w (λ w' e' → inOpenBar' w' (↑'inOpenBar i e') (↑wPredDep' g e'))
                  → inOpenBar' w i g
inOpenBar'-idem {w} {f} {g} i h w1 e1 =
  w4 , e4 ,  h5
  where
    w1' : 𝕎·
    w1' = fst (i w1 e1)

    e1' : w1 ⊑· w1'
    e1' = fst (snd (i w1 e1))

    w2 : 𝕎·
    w2 = fst (h w1' (⊑-trans· e1 e1'))

    e2 : w1' ⊑· w2
    e2 = fst (snd (h w1' (⊑-trans· e1 e1')))

    h2 : ∀𝕎 w2 (λ w' e' → (z : w ⊑· w') → inOpenBar' w' (↑'inOpenBar i z)  (↑wPredDep' g z))
    h2 = snd (snd (h w1' (⊑-trans· e1 e1')))

    h3 : inOpenBar' w2 (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2)) (↑wPredDep' g (⊑-trans· (⊑-trans· e1 e1') e2))
    h3 = h2 w2 (⊑-refl· w2) (⊑-trans· (⊑-trans· e1 e1') e2)

    w3 : 𝕎·
    w3 = fst (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))

    e3 : w2 ⊑· w3
    e3 = fst (snd (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2)))

    h4 : ∃∀𝕎 w3 (λ w' e' → (z : w2 ⊑· w')
                            → ↑wPredDep'
                                g
                                (⊑-trans· (⊑-trans· e1 e1') e2)
                                w' z
                                (snd (snd (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))) w' e' z))
    h4 = h3 w2 (⊑-refl· w2)

    w4 : 𝕎·
    w4 = fst h4

    e4 : w1' ⊑· w4
    e4 = ⊑-trans· (⊑-trans· e2 e3) (fst (snd h4))

    h5 : ∀𝕎 w4 (λ w' e' → (z : w ⊑· w') → g w' z (snd (snd (i w1 e1)) w' (⊑-trans· e4 e') z))
    h5 w5 e5 z = a2
      where
        a1 : ↑wPredDep' g
                        (⊑-trans· (⊑-trans· e1 e1') e2)
                        w5 (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5)
                        (snd (snd (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))) w5 (⊑-trans· (fst (snd h4)) e5) (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5))
        a1 = snd (snd h4) w5 e5 (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5)

        a2 : g w5 z (snd (snd (i w1 e1)) w5 (⊑-trans· e4 e5) z)
        a2 = a1 z (snd (snd (i w1 e1)) w5 (⊑-trans· e4 e5) z)




inOpenBar'-idem2 : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                   → wPredDepExtIrr-inOpenBar g i
                   → inOpenBar w (λ w' e' → inOpenBar' w' (↑inOpenBar i e') (↑wPredDep g e'))
                   → inOpenBar' w i g
inOpenBar'-idem2 {w} {f} {g} i ext h w1 e1 =
  fst h4 ,
  ⊑-trans· (⊑-trans· e2 e3) (fst (snd h4)),
  λ w5 e5 z → ext w2 w1 w5
                  (⊑-trans· (⊑-trans· (⊑-trans· e1 e1') e2) (⊑-refl· w2)) e1 z
                  (⊑-trans· (fst (snd h4)) e5)
                  (⊑-trans· (⊑-trans· (⊑-trans· e2 e3) (fst (snd h4))) e5)
                  (⊑-trans· (⊑-trans· (⊑-trans· e1 e1') e2) (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5))
                  (snd (snd h4) w5 e5 (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5))
  where
    w1' : 𝕎·
    w1' = fst (i w1 e1)

    e1' : w1 ⊑· w1'
    e1' = fst (snd (i w1 e1))

    w2 : 𝕎·
    w2 = fst (h w1' (⊑-trans· e1 e1'))

    e2 : w1' ⊑· w2
    e2 = fst (snd (h w1' (⊑-trans· e1 e1')))

    h2 : ∀𝕎 w2 (λ w' e' → (z : w ⊑· w') → inOpenBar' w' (↑inOpenBar i z)  (↑wPredDep g z))
    h2 = snd (snd (h w1' (⊑-trans· e1 e1')))

    h3 : inOpenBar' w2 (↑inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2)) (↑wPredDep g (⊑-trans· (⊑-trans· e1 e1') e2))
    h3 = h2 w2 (⊑-refl· w2) (⊑-trans· (⊑-trans· e1 e1') e2)

    w3 : 𝕎·
    w3 = fst (↑inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))

    e3 : w2 ⊑· w3
    e3 = fst (snd (↑inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2)))

    h4 : ∃∀𝕎 w3 (λ w' e' → (z : w2 ⊑· w')
                            → ↑wPredDep
                                g
                                (⊑-trans· (⊑-trans· e1 e1') e2)
                                w' z
                                (snd (snd (↑inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))) w' e' z))
    h4 = h3 w2 (⊑-refl· w2)




inOpenBar'-comb : {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : inOpenBar w f)
              → ∀𝕎 w (λ w' e' → (z : f w' e') (zg : f w' e') (zh : f w' e')
                                 → g w' e' zg → h w' e' zh → k w' e' z)
              → inOpenBar' w i g → inOpenBar' w i h → inOpenBar' w i k
inOpenBar'-comb {w} {f} {g} {h} {k} i aw ig ih w1 e1 =
  w5 ,
  ⊑-trans· (⊑-trans· e3 e4) e5 ,
  λ w6 e6 z → aw w6 z
                 (snd (snd (i w1 e1)) w6 (⊑-trans· (⊑-trans· (⊑-trans· (proj₁ (snd (ih w1 e1))) e4) e5) e6) z)
                 (h4 w6 (⊑-trans· e5 e6) z) (h2 w6 (⊑-trans· e3 (⊑-trans· (⊑-trans· e4 e5) e6)) z)
                 (h5 w6 e6 z)
                 (h3 w6 (⊑-trans· (⊑-trans· e4 e5) e6) z)
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h2 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h2 = snd (snd (i w1 e1))

    w3 : 𝕎·
    w3 = fst (ih w1 e1)

    e3 : w2 ⊑· w3
    e3 = fst (snd (ih w1 e1))

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w ⊑· w4) → h w4 z (h2 w4 (⊑-trans· e3 e4) z))
    h3 = snd (snd (ih w1 e1))

    w4 : 𝕎·
    w4 = fst (i w3 (⊑-trans· (⊑-trans· e1 e2) e3))

    e4 : w3 ⊑· w4
    e4 = fst (snd (i w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    h4 : ∀𝕎 w4 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h4 = snd (snd (i w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    w5 : 𝕎·
    w5 = fst (ig w3 (⊑-trans· (⊑-trans· e1 e2) e3))

    e5 : w4 ⊑· w5
    e5 = fst (snd (ig w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    h5 : ∀𝕎 w5 (λ w6 e6 → (z : w ⊑· w6) → g w6 z (h4 w6 (⊑-trans· e5 e6) z))
    h5 = snd (snd (ig w3 (⊑-trans· (⊑-trans· e1 e2) e3)))




∀𝕎-inOpenBar-inOpenBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                            → ∀𝕎 w (λ w' e' → (x : f w' e') (at : atOpenBar i w' e' x) → g w' e' x)
                            → inOpenBar' w i g
∀𝕎-inOpenBar-inOpenBar' {w} {f} {g} i h w1 e1 =
  w2 ,
  ⊑-refl· w2 ,
  λ w3 e3 z → h w3 z (h0 w3 (⊑-trans· (⊑-refl· w2) e3) z) (ATOPENBAR w1 e1 w3 (⊑-trans· (⊑-refl· (fst (i w1 e1))) e3) z)
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h0 = snd (snd (i w1 e1))



inOpenBar-mon : {w2 w1 : 𝕎·} {f :  wPred w1} (e : w1 ⊑· w2)
                → inOpenBar w1 f
                → inOpenBar w2 (↑wPred f e)
inOpenBar-mon {w2} {w1} {f} e h w' e' = w'' , e'' , h''
  where
    w'' : 𝕎·
    w'' = fst (h w' (⊑-trans· e e'))

    e'' : w' ⊑· w''
    e'' = fst (snd (h w' (⊑-trans· e e')))

    h'' : ∀𝕎 w'' (λ w3 e3 → (z : w2 ⊑· w3) → ↑wPred f e w3 z)
    h'' w3 e3 z = snd (snd (h w' (⊑-trans· e e'))) w3 e3 (⊑-trans· e z)




∀𝕎-inOpenBar : {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → inOpenBar w f
∀𝕎-inOpenBar {w} {f} h w1 e1 =  w1 , ⊑-refl· w1 , λ w2 e2 z → h w2 z



inOpenBar-idem : {w : 𝕎·} {f : wPred w}
                 → inOpenBar w (λ w1 e1 → inOpenBar w1 (↑wPred' f e1))
                 → inOpenBar w f
inOpenBar-idem {w} {f} h w1 e1 =
  fst h4 ,
  ⊑-trans· e2 (fst (snd h4)) ,
  λ w3 e3 z → snd (snd h4) w3 e3 (⊑-trans· (fst (snd h4)) e3) z
  where
    w2 : 𝕎·
    w2 = fst (h w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (h w1 e1))

    h2 : ∀𝕎 w2 (λ w' e' → (z : w ⊑· w') → inOpenBar w' (↑wPred' f z))
    h2 = snd (snd (h w1 e1))

    h3 : inOpenBar w2 (↑wPred' f (⊑-trans· e1 e2))
    h3 = h2 w2 (⊑-refl· w2) (⊑-trans· e1 e2)

    h4 : ∃∀𝕎 w2 (λ w' e' → (z : w2 ⊑· w') → (z' : w ⊑· w') → f w' z')
    h4 = h3 w2 (⊑-refl· w2)



inOpenBar-idem2 : {w : 𝕎·} {f : wPred w}
                  → wPredExtIrr f
                  → inOpenBar w (λ w1 e1 → inOpenBar w1 (↑wPred f e1))
                  → inOpenBar w f
inOpenBar-idem2 {w} {f} ext h w1 e1 =
  fst h4 ,
  ⊑-trans· e2 (fst (snd h4)) ,
  h5
  where
    w2 : 𝕎·
    w2 = fst (h w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (h w1 e1))

    h2 : ∀𝕎 w2 (λ w' e' → (z : w ⊑· w') → inOpenBar w' (↑wPred f z))
    h2 = snd (snd (h w1 e1))

    h3 : inOpenBar w2 (↑wPred f (⊑-trans· e1 e2))
    h3 = h2 w2 (⊑-refl· w2) (⊑-trans· e1 e2)

    h4 : ∃∀𝕎 w2 (λ w' e' → (z : w2 ⊑· w') → f w' (⊑-trans· (⊑-trans· e1 e2) z))
    h4 = h3 w2 (⊑-refl· w2)

    h5 : ∀𝕎 (proj₁ h4) (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h5 w3 e3 z = ext w3 _ z (snd (snd h4) w3 e3 (⊑-trans· (fst (snd h4)) e3))



∀𝕎-inOpenBar'-inOpenBar-old : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w}
                                → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                                → (i : inOpenBar w f) → inOpenBar' w i g → inOpenBar w h
∀𝕎-inOpenBar'-inOpenBar-old {w} {f} {g} {h} a i q w1 e1 =
  w3 , ⊑-trans· e2 e3 , λ w4 e4 z → a w4 z (h0 w4 (⊑-trans· e3 e4) z) (h3 w4 e4 z)
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h0 = snd (snd (i w1 e1))

    w3 : 𝕎·
    w3 = fst (q w1 e1)

    e3 : w2 ⊑· w3
    e3 = fst (snd (q w1 e1))

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w ⊑· w4) → g w4 z (h0 w4 (⊑-trans· e3 e4) z))
    h3 = snd (snd (q w1 e1))



∀𝕎-inOpenBar'-inOpenBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inOpenBar w f)
                            → ∀𝕎 w (λ w' e' → (x : f w' e') → atOpenBar i w' e' x → g w' e' x → h w' e')
                            → inOpenBar' w i g → inOpenBar w h
∀𝕎-inOpenBar'-inOpenBar {w} {f} {g} {h} i a q w1 e1 =
  w3 , ⊑-trans· e2 e3 , λ w4 e4 z → a w4 z (h0 w4 (⊑-trans· e3 e4) z) (ATOPENBAR w1 e1 w4 (⊑-trans· e3 e4) z) (h3 w4 e4 z)
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h0 = snd (snd (i w1 e1))

    w3 : 𝕎·
    w3 = fst (q w1 e1)

    e3 : w2 ⊑· w3
    e3 = fst (snd (q w1 e1))

    h3 : ∀𝕎 w3 (λ w4 e4 → (z : w ⊑· w4) → g w4 z (h0 w4 (⊑-trans· e3 e4) z))
    h3 = snd (snd (q w1 e1))



inOpenBar-const : {w : 𝕎·} {t : Set₁} → inOpenBar w (λ w e → t) → t
inOpenBar-const {w} {t} h = snd (snd (h w (⊑-refl· w))) (fst (h w (⊑-refl· w))) (⊑-refl· _) (fst (snd (h w (⊑-refl· w))))




old-inOpenBar'-change : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i j : inOpenBar w f)
                    → ∀𝕎 w (λ w' e' → (x y : f w' e') → atOpenBar i w' e' x → atOpenBar j w' e' y → g w' e' x → g w' e' y)
                    → inOpenBar' w i g → inOpenBar' w j g
old-inOpenBar'-change {w} {f} {g} i j aw b w1 e1 =
  w4 , ⊑-trans· e3 e4 , h1
  where
    w2 : 𝕎·
    w2 = fst (j w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (j w1 e1))

    w3 : 𝕎·
    w3 = fst (i w2 (⊑-trans· e1 e2))

    e3 : w2 ⊑· w3
    e3 = fst (snd (i w2 (⊑-trans· e1 e2)))

    w4 : 𝕎·
    w4 = fst (b w2 (⊑-trans· e1 e2))

    e4 : w3 ⊑· w4
    e4 = fst (snd (b w2 (⊑-trans· e1 e2)))

    h0 : ∀𝕎 w4 (λ w5 e5 → (z : w ⊑· w5) → g w5 z (snd (snd (i w2 (⊑-trans· e1 e2))) w5 (⊑-trans· e4 e5) z))
    h0 = snd (snd (b w2 (⊑-trans· e1 e2)))

    h1 : ∀𝕎 w4 (λ w5 e5 → (z : w ⊑· w5) → g w5 z (snd (snd (j w1 e1)) w5 (⊑-trans· (⊑-trans· e3 e4) e5) z))
    h1 w5 e5 z =
      aw w5 z
         (snd (snd (i w2 (⊑-trans· e1 e2))) w5 (⊑-trans· e4 e5) z)
         (snd (snd (j w1 e1)) w5 (⊑-trans· (⊑-trans· e3 e4) e5) z)
         (ATOPENBAR w2 (⊑-trans· e1 e2) w5  (⊑-trans· e4 e5) z)
         (ATOPENBAR w1 e1 w5  (⊑-trans· (⊑-trans· e3 e4) e5) z)
         (h0 w5 e5 z)



inOpenBar'-change : {w : 𝕎·} {f : wPred w} {k : wPred w} {g : wPredDep f} {h : wPredDep k}
                    (i : inOpenBar w f) (j : inOpenBar w k)
                    → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e') → atOpenBar i w' e' x → atOpenBar j w' e' y
                                      → g w' e' x → h w' e' y)
                    → inOpenBar' w i g → inOpenBar' w j h
inOpenBar'-change {w} {f} {k} {g} {h} i j aw b w1 e1 =
  w4 , ⊑-trans· e3 e4 , h1
  where
    w2 : 𝕎·
    w2 = fst (j w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (j w1 e1))

    w3 : 𝕎·
    w3 = fst (i w2 (⊑-trans· e1 e2))

    e3 : w2 ⊑· w3
    e3 = fst (snd (i w2 (⊑-trans· e1 e2)))

    w4 : 𝕎·
    w4 = fst (b w2 (⊑-trans· e1 e2))

    e4 : w3 ⊑· w4
    e4 = fst (snd (b w2 (⊑-trans· e1 e2)))

    h0 : ∀𝕎 w4 (λ w5 e5 → (z : w ⊑· w5) → g w5 z (snd (snd (i w2 (⊑-trans· e1 e2))) w5 (⊑-trans· e4 e5) z))
    h0 = snd (snd (b w2 (⊑-trans· e1 e2)))

    h1 : ∀𝕎 w4 (λ w5 e5 → (z : w ⊑· w5) → h w5 z (snd (snd (j w1 e1)) w5 (⊑-trans· (⊑-trans· e3 e4) e5) z))
    h1 w5 e5 z =
      aw w5 z
         (snd (snd (i w2 (⊑-trans· e1 e2))) w5 (⊑-trans· e4 e5) z)
         (snd (snd (j w1 e1)) w5 (⊑-trans· (⊑-trans· e3 e4) e5) z)
         (ATOPENBAR w2 (⊑-trans· e1 e2) w5 (⊑-trans· e4 e5) z)
         (ATOPENBAR w1 e1 w5 (⊑-trans· (⊑-trans· e3 e4) e5) z)
         (h0 w5 e5 z)



-- We can prove that open-bars satisfy the Bar properties
inOpenBar-Bar : Bar
inOpenBar-Bar =
  mkBar
    inOpenBar
    inOpenBar'
--    wPredDepExtIrr-inOpenBar
    ↑inOpenBar
    ↑'inOpenBar
--    (λ {w} {f} {g} → ↑inOpenBar' {w} {f} {g})
--    atOpenBar
    atOpenBar
    inOpenBarFunc
    ∀𝕎-inOpenBarFunc
    inOpenBar-inOpenBar'
    --(λ {w} {f} {g} {h} → inOpenBar'-inOpenBar' {w} {f} {g} {h})
    ∀𝕎-inOpenBar-inOpenBar'
    ∀𝕎-inOpenBar
--    inOpenBar-mon
    inOpenBar-idem
--    inOpenBar-idem2
    (λ {w} {f} {g} → inOpenBar'-idem {w} {f} {g})
--    (λ {w} {f} {g} → inOpenBar'-idem2 {w} {f} {g})
    {--∀𝕎-inOpenBar'-inOpenBar--}
    ∀𝕎-inOpenBar'-inOpenBar
    inOpenBar'-comb
--    old-inOpenBar'-change
    inOpenBar'-change
    inOpenBar-const
\end{code}
