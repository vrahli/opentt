\begin{code}
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import world


module bar where


-- TODO:
--   remove [allW-inBar'-inBar], keep only [allW-inBar'-inBar2]
--   try to remove [inBar-idem2] and [inBar'-idem2]

record Bar : Set₂ where
  constructor mkBar
  field
    -- Operators
    inBar             : (w : world) (f : wPred w) → Set₁
    inBar'            : (w : world) {g : wPred w} (h : inBar w g) (f : wPredDep g) → Set₁
    wPredDepExtIrrBar : {w : world} {f : wPred w} (h : wPredDep f) (i : inBar w f) → Set₁
    ↑inBar            : {w : world} {f : wPred w} (i : inBar w f) {w' : world} (e : w' ≽ w) → inBar w' (↑wPred f e)
    ↑'inBar           : {w : world} {f : wPred w} (i : inBar w f) {w' : world} (e : w' ≽ w) → inBar w' (↑wPred' f e)
--    atBar             : {w : world} {f : wPred w} (i : inBar w f) (w' : world) → Set₁
    atBar             : {w : world} {f : wPred w} (i : inBar w f) (w' : world) (e' : w' ≽ w) (p : f w' e') → Set₁
    -- Axioms
    inBarFunc         : {w : world} {f g : wPred w}
                        → inBar w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    allW-inBarFunc    : {w : world} {f g : wPred w}
                        → allW w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    inBar-inBar'      : {w : world} {f : wPred w} {g : wPredDep f}
                        → inBar w (λ w' e' → (x : f w' e') → g w' e' x)
                        → (i : inBar w f) → inBar' w i g
{--    inBar'-inBar'      : {w : world} {f : wPred w} {g : wPredDep f} {h : wPredDep f} (i : inBar w f)
                         → wPredDepExtIrrBar g i
                         → wPredDepExtIrrBar h i
                         → inBar' w i (λ w' e' z → g w' e' z → h w' e' z)
                         → inBar' w i g → inBar' w i h--}
    allW-inBar-inBar' : {w : world} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → allW w (λ w' e' → (x : f w' e') (at : atBar i w' e' x) → g w' e' x)
                        → inBar' w i g
    allW-inBar        : {w : world} {f : wPred w} → allW w f → inBar w f
    inBar-mon         : {w2 w1 : world} {f : wPred w1} (e : w2 ≽ w1)
                        → inBar w1 f → inBar w2 (↑wPred f e)
    inBar-idem        : {w : world} {f : wPred w}
                        → inBar w (λ w' e' → inBar w' (↑wPred' f e'))
                        → inBar w f
    inBar-idem2       : {w : world} {f : wPred w}
                        → wPredExtIrr f
                        → inBar w (λ w' e' → inBar w' (↑wPred f e'))
                        → inBar w f
    inBar'-idem       : {w : world} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → inBar w (λ w' e' → inBar' w' (↑'inBar i e') (↑wPredDep' g e'))
                        → inBar' w i g
    inBar'-idem2      : {w : world} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → wPredDepExtIrrBar g i
                        → inBar w (λ w' e' → inBar' w' (↑inBar i e') (↑wPredDep g e'))
                        → inBar' w i g
{--    allW-inBar'-inBar : {w : world} {f : wPred w} {g : wPredDep f} {h : wPred w}
                        → allW w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                        → (i : inBar w f) → inBar' w i g → inBar w h--}
    allW-inBar'-inBar : {w : world} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inBar w f)
                        → allW w (λ w' e' → (x : f w' e') → atBar i w' e' x → g w' e' x → h w' e')
                        → inBar' w i g → inBar w h
    inBar'-comb       : {w : world} {f : wPred w} {g h k : wPredDep f} (i : inBar w f)
                        → allW w (λ w' e' → (z zg zh : f w' e')
                                           → g w' e' zg → h w' e' zh → k w' e' z)
                        → inBar' w i g → inBar' w i h → inBar' w i k
    inBar'-change     : {w : world} {f : wPred w} {g : wPredDep f} (i j : inBar w f)
                        → allW w (λ w' e' → (x y : f w' e') → atBar i w' e' x → atBar j w' e' y → g w' e' x → g w' e' y)
                        → inBar' w i g → inBar' w j g
    inBar-const       : {w : world} {t : Set₁} → inBar w (λ w e → t) → t


-- This is a consequence of [allW-inBar'-inBar]
inBar'-inBar : (b : Bar)
               {w : world} {f : wPred w} {h : wPred w}
               → (i : Bar.inBar b w f) → Bar.inBar' b w i (λ w1 e1 z → h w1 e1) → Bar.inBar b w h
inBar'-inBar b {w} {f} {h} i q = Bar.allW-inBar'-inBar b i (λ w1 e1 x at z → z) q


-- This is a consequence of [inBar'-comb] for 3 dependent bars
inBar'3 : (b : Bar) {w : world} {f : wPred w} {g h k j : wPredDep f} (i : Bar.inBar b w f)
          → allW w (λ w' e' → (z : f w' e') (zg : f w' e') (zh : f w' e') (zk : f w' e')
                             → g w' e' zg → h w' e' zh → k w' e' zk → j w' e' z)
          → Bar.inBar' b w i g → Bar.inBar' b w i h → Bar.inBar' b w i k → Bar.inBar' b w i j
inBar'3 b {w} {f} {g} {h} {k} {j} i imp ig ih ik = c
  where
    ip : Bar.inBar' b w i (λ w1 e1 z → Σ (f w1 e1) λ zg → Σ (f w1 e1) λ zh → g w1 e1 zg × h w1 e1 zh)
    ip = Bar.inBar'-comb b i (λ w1 e1 z zg zh xg xh → zg , zh , xg , xh) ig ih

    c : Bar.inBar' b w i j
    c = Bar.inBar'-comb b i (λ w1 e1 zj zh zk (zg' , zh' , ig , ih) ik → imp w1 e1 zj zg' zh' zk ig ih ik) ip ik


-- f holds in an open bar
inOpenBar : (w : world) (f : wPred w) → Set₁
inOpenBar w f =
  allW w (λ w1 e1 → exW w1 (λ w2 e2 → allW w2 (λ w3 e3 →
     (z : w3 ≽ w) → f w3 z)))


-- f holds in an open bar that depends on another open bar h
inOpenBar' : (w : world) {g : wPred w} (h : inOpenBar w g) (f : wPredDep g) → Set₁
inOpenBar' w h f =
  allW w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exAllW w1 (λ w2 e2 → (z : w2 ≽ w) → f w2 z (q w2 e2 z)))


wPredDepExtIrr-inOpenBar : {w : world} {f : wPred w} (h : wPredDep f) (i : inOpenBar w f) → Set₁
wPredDepExtIrr-inOpenBar {w} {f} h i =
  (w0 w1 w2 : world) (e0 : w0 ≽ w) (e1 : w1 ≽ w) (e2 : w2 ≽ w)
  (e0' : w2 ≽ fst (i w0 e0)) (e1' : w2 ≽ fst (i w1 e1)) (e2' : w2 ≽ w)
  → h w2 e2' (snd (snd (i w0 e0)) w2 e0' e2')
  → h w2 e2 (snd (snd (i w1 e1)) w2 e1' e2)


inOpenBarFunc : {w : world} {f g : wPred w} → inOpenBar w (λ w' e' → f w' e' → g w' e') → inOpenBar w f → inOpenBar w g
inOpenBarFunc {w} {f} {g} F h w1 e1 =
  fst h2 , extTrans (fst (snd h2)) e2 , h3
  where
    h1 : exAllW w1 λ w2 e2 → (z : w2 ≽ w) → f w2 z
    h1 = h w1 e1

    w2 : world
    w2 = fst h1

    e2 : w2 ≽ w1
    e2 = fst (snd h1)

    h2 : exAllW w2 (λ w' e' → (z : w' ≽ w) → f w' z → g w' z)
    h2 = F w2 (extTrans e2 e1)

    w3 : world
    w3 = fst h2

    e3 : w3 ≽ w2
    e3 = fst (snd h2)

    h3 : allW w3 (λ w4 e4 → (z : w4 ≽ w) → g w4 z)
    h3 w4 e4 z = snd (snd h2) w4 e4 z (snd (snd h1) w4 (extTrans e4 e3) z)


allW-inOpenBarFunc : {w : world} {f g : wPred w} → allW w (λ w' e' → f w' e' → g w' e') → inOpenBar w f → inOpenBar w g
allW-inOpenBarFunc {w} {f} {g} F h w1 e1 =
  w2 , e2 , h3
  where
    h1 : exAllW w1 λ w2 e2 → (z : w2 ≽ w) → f w2 z
    h1 = h w1 e1

    w2 : world
    w2 = fst h1

    e2 : w2 ≽ w1
    e2 = fst (snd h1)

    h2 : allW w2 λ w3 e3 → (z : w3 ≽ w) → f w3 z
    h2 = snd (snd h1)

    h3 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → g w3 z)
    h3 w3 e3 z = F w3 z (h2 w3 e3 z)


inOpenBar-inOpenBar' : {w : world} {f : wPred w} {g : wPredDep f}
                       → inOpenBar w (λ w' e' → (x : f w' e') → g w' e' x)
                       → (i : inOpenBar w f) → inOpenBar' w i g
inOpenBar-inOpenBar' {w} {f} {g} h i w1 e1 = w3 , e3 , h3
  where
    w2 : world
    w2 = fst (i w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (i w1 e1))

    h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h0 = snd (snd (i w1 e1))

    h1 : exAllW w2 (λ w' e' → (z : w' ≽ w) (x : f w' z) → g w' z x)
    h1 = h w2 (extTrans e2 e1)

    w3 : world
    w3 = fst h1

    e3 : w3 ≽ w2
    e3 = fst (snd h1)

    h2 : allW w3 (λ w' e' → (z : w' ≽ w) (x : f w' z) → g w' z x)
    h2 = snd (snd h1)

    h3 : allW w3 (λ w4 e4 → (z : w4 ≽ w) → g w4 z (h0 w4 (extTrans e4 e3) z))
    h3 w4 e4 z = h2 w4 e4 z (h0 w4 (extTrans e4 e3) z)



inOpenBar'-inOpenBar' : {w : world} {f : wPred w} {g h : wPredDep f} (i : inOpenBar w f)
                        → wPredDepExtIrr-inOpenBar g i
                        → wPredDepExtIrr-inOpenBar h i
                        → inOpenBar' w i (λ w' e' z → g w' e' z → h w' e' z)
                        → inOpenBar' w i g → inOpenBar' w i h
inOpenBar'-inOpenBar' {w} {f} {g} {h} i irrg irrh j o w1 e1 =
  w5 ,
  extTrans e5 (extTrans e4 e3) ,
  λ w6 e6 z →
    irrh
      w3 w1 w6
      (extTrans e3 (extTrans e2 e1)) e1 z
      (extTrans e6 e5)
      (extTrans e6 (extTrans e5 (extTrans e4 e3)))
      z
      (h5 w6 e6 z (irrg
                     w1 w3 w6
                     e1 (extTrans e3 (extTrans e2 e1)) z
                     (extTrans (extTrans e6 (extTrans e5 e4)) e3)
                     (extTrans e6 e5)
                     z
                     (h3 w6 (extTrans e6 (extTrans e5 e4)) z)))
  where
    w2 : world
    w2 = fst (i w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (i w1 e1))

    h2 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h2 = snd (snd (i w1 e1))

    w3 : world
    w3 = fst (o w1 e1)

    e3 : w3 ≽ w2
    e3 = fst (snd (o w1 e1))

    h3 : allW w3 (λ w4 e4 → (z : w4 ≽ w) → g w4 z (h2 w4 (extTrans e4 e3) z))
    h3 = snd (snd (o w1 e1))

    w4 : world
    w4 = fst (i w3 (extTrans e3 (extTrans e2 e1)))

    e4 : w4 ≽ w3
    e4 = fst (snd (i w3 (extTrans e3 (extTrans e2 e1))))

    h4 : allW w4 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h4 = snd (snd (i w3 (extTrans e3 (extTrans e2 e1))))

    w5 : world
    w5 = fst (j w3 (extTrans e3 (extTrans e2 e1)))

    e5 : w5 ≽ w4
    e5 = fst (snd (j w3 (extTrans e3 (extTrans e2 e1))))

    h5 : allW w5 (λ w6 e6 → (z : w6 ≽ w) → g w6 z (h4 w6 (extTrans e6 e5) z) → h w6 z (h4 w6 (extTrans e6 e5) z))
    h5 = snd (snd (j w3 (extTrans e3 (extTrans e2 e1))))



↑inOpenBar : {w1 : world} {f : wPred w1} (i : inOpenBar w1 f) {w2 : world} (e : w2 ≽ w1) → inOpenBar w2 (↑wPred f e)
↑inOpenBar {w1} {f} i {w2} e w' e' = w0 , e0 , h0
  where
    w0 : world
    w0 = fst (i w' (extTrans e' e))

    e0 : w0 ≽ w'
    e0 = fst (snd (i w' (extTrans e' e)))

    h0 : allW w0 (λ w3 e3 → (z : w3 ≽ w2) → ↑wPred f e w3 z)
    h0 w3 e3 z = snd (snd (i w' (extTrans e' e))) w3 e3 (extTrans z e)



↑'inOpenBar : {w1 : world} {f : wPred w1} (i : inOpenBar w1 f) {w2 : world} (e : w2 ≽ w1) → inOpenBar w2 (↑wPred' f e)
↑'inOpenBar {w1} {f} i {w2} e w' e' = w0 , e0 , h0
  where
    w0 : world
    w0 = fst (i w' (extTrans e' e))

    e0 : w0 ≽ w'
    e0 = fst (snd (i w' (extTrans e' e)))

    h0 : allW w0 (λ w3 e3 → (z : w3 ≽ w2) → ↑wPred' f e w3 z)
    h0 w3 e3 z x = snd (snd (i w' (extTrans e' e))) w3 e3 x




--atOpenBar : {w : world} {f : wPred w} (i : inOpenBar w f) (w' : world) → Set₁
--atOpenBar {w} {f} i w' = Σ world (λ w1 → Σ (w1 ≽ w) (λ e1 → w' ≽ fst (i w1 e1)))
-- --  Σ (w' ≽ fst (i w1 e1)) (λ e2 → snd (snd (i w1 e1)) w' e2 e)))


data atOpenBar {w : world} {f : wPred w} (i : inOpenBar w f) : (w' : world) (e' : w' ≽ w) (p : f w' e') → Set₁
data atOpenBar {w} {f} i where
  ATOPENBAR : (w1 : world) (e1 : w1 ≽ w) (w2 : world) (e2 : w2 ≽ fst (i w1 e1)) (z : w2 ≽ w)
              → atOpenBar {w} {f} i w2 z (snd (snd (i w1 e1)) w2 e2 z)





inOpenBar'-idem : {w : world} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                  → inOpenBar w (λ w' e' → inOpenBar' w' (↑'inOpenBar i e') (↑wPredDep' g e'))
                  → inOpenBar' w i g
inOpenBar'-idem {w} {f} {g} i h w1 e1 =
  w4 , e4 ,  h5
  where
    w1' : world
    w1' = fst (i w1 e1)

    e1' : w1' ≽ w1
    e1' = fst (snd (i w1 e1))

    w2 : world
    w2 = fst (h w1' (extTrans e1' e1))

    e2 : w2 ≽ w1'
    e2 = fst (snd (h w1' (extTrans e1' e1)))

    h2 : allW w2 (λ w' e' → (z : w' ≽ w) → inOpenBar' w' (↑'inOpenBar i z)  (↑wPredDep' g z))
    h2 = snd (snd (h w1' (extTrans e1' e1)))

    h3 : inOpenBar' w2 (↑'inOpenBar i (extTrans e2 (extTrans e1' e1))) (↑wPredDep' g (extTrans e2 (extTrans e1' e1)))
    h3 = h2 w2 (extRefl w2) (extTrans e2 (extTrans e1' e1))

    w3 : world
    w3 = fst (↑'inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2))

    e3 : w3 ≽ w2
    e3 = fst (snd (↑'inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2)))

    h4 : exAllW w3 (λ w' e' → (z : w' ≽ w2)
                            → ↑wPredDep'
                                g
                                (extTrans e2 (extTrans e1' e1))
                                w' z
                                (snd (snd (↑'inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2))) w' e' z))
    h4 = h3 w2 (extRefl w2)

    w4 : world
    w4 = fst h4

    e4 : w4 ≽ w1'
    e4 = extTrans (fst (snd h4)) (extTrans e3 e2)

    h5 : allW w4 (λ w' e' → (z : w' ≽ w) → g w' z (snd (snd (i w1 e1)) w' (extTrans e' e4) z))
    h5 w5 e5 z = a2
      where
        a1 : ↑wPredDep' g
                        (extTrans e2 (extTrans e1' e1))
                        w5 (extTrans e5 (extTrans (fst (snd h4)) e3))
                        (snd (snd (↑'inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2))) w5 (extTrans e5 (fst (snd h4))) (extTrans e5 (extTrans (fst (snd h4)) e3)))
        a1 = snd (snd h4) w5 e5 (extTrans e5 (extTrans (fst (snd h4)) e3))

        a2 : g w5 z (snd (snd (i w1 e1)) w5 (extTrans e5 e4) z)
        a2 = a1 z (snd (snd (i w1 e1)) w5 (extTrans e5 e4) z)




inOpenBar'-idem2 : {w : world} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                   → wPredDepExtIrr-inOpenBar g i
                   → inOpenBar w (λ w' e' → inOpenBar' w' (↑inOpenBar i e') (↑wPredDep g e'))
                   → inOpenBar' w i g
inOpenBar'-idem2 {w} {f} {g} i ext h w1 e1 =
  fst h4 ,
  extTrans (fst (snd h4)) (extTrans e3 e2),
  λ w5 e5 z → ext w2 w1 w5
                  (extTrans (extRefl w2) (extTrans e2 (extTrans e1' e1))) e1 z
                  (extTrans e5 (fst (snd h4)))
                  (extTrans e5 (extTrans (fst (snd h4)) (extTrans e3 e2)))
                  (extTrans (extTrans e5 (extTrans (fst (snd h4)) e3)) (extTrans e2 (extTrans e1' e1)))
                  (snd (snd h4) w5 e5 (extTrans e5 (extTrans (fst (snd h4)) e3)))
  where
    w1' : world
    w1' = fst (i w1 e1)

    e1' : w1' ≽ w1
    e1' = fst (snd (i w1 e1))

    w2 : world
    w2 = fst (h w1' (extTrans e1' e1))

    e2 : w2 ≽ w1'
    e2 = fst (snd (h w1' (extTrans e1' e1)))

    h2 : allW w2 (λ w' e' → (z : w' ≽ w) → inOpenBar' w' (↑inOpenBar i z)  (↑wPredDep g z))
    h2 = snd (snd (h w1' (extTrans e1' e1)))

    h3 : inOpenBar' w2 (↑inOpenBar i (extTrans e2 (extTrans e1' e1))) (↑wPredDep g (extTrans e2 (extTrans e1' e1)))
    h3 = h2 w2 (extRefl w2) (extTrans e2 (extTrans e1' e1))

    w3 : world
    w3 = fst (↑inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2))

    e3 : w3 ≽ w2
    e3 = fst (snd (↑inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2)))

    h4 : exAllW w3 (λ w' e' → (z : w' ≽ w2)
                            → ↑wPredDep
                                g
                                (extTrans e2 (extTrans e1' e1))
                                w' z
                                (snd (snd (↑inOpenBar i (extTrans e2 (extTrans e1' e1)) w2 (extRefl w2))) w' e' z))
    h4 = h3 w2 (extRefl w2)




inOpenBar'-comb : {w : world} {f : wPred w} {g h k : wPredDep f} (i : inOpenBar w f)
              → allW w (λ w' e' → (z : f w' e') (zg : f w' e') (zh : f w' e')
                                 → g w' e' zg → h w' e' zh → k w' e' z)
              → inOpenBar' w i g → inOpenBar' w i h → inOpenBar' w i k
inOpenBar'-comb {w} {f} {g} {h} {k} i aw ig ih w1 e1 =
  w5 ,
  extTrans e5 (extTrans e4 e3) ,
  λ w6 e6 z → aw w6 z
                 (snd (snd (i w1 e1)) w6 (extTrans e6 (extTrans e5 (extTrans e4 (proj₁ (snd (ih w1 e1)))))) z)
                 (h4 w6 (extTrans e6 e5) z) (h2 w6 (extTrans (extTrans e6 (extTrans e5 e4)) e3) z)
                 (h5 w6 e6 z)
                 (h3 w6 (extTrans e6 (extTrans e5 e4)) z)
  where
    w2 : world
    w2 = fst (i w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (i w1 e1))

    h2 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h2 = snd (snd (i w1 e1))

    w3 : world
    w3 = fst (ih w1 e1)

    e3 : w3 ≽ w2
    e3 = fst (snd (ih w1 e1))

    h3 : allW w3 (λ w4 e4 → (z : w4 ≽ w) → h w4 z (h2 w4 (extTrans e4 e3) z))
    h3 = snd (snd (ih w1 e1))

    w4 : world
    w4 = fst (i w3 (extTrans e3 (extTrans e2 e1)))

    e4 : w4 ≽ w3
    e4 = fst (snd (i w3 (extTrans e3 (extTrans e2 e1))))

    h4 : allW w4 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h4 = snd (snd (i w3 (extTrans e3 (extTrans e2 e1))))

    w5 : world
    w5 = fst (ig w3 (extTrans e3 (extTrans e2 e1)))

    e5 : w5 ≽ w4
    e5 = fst (snd (ig w3 (extTrans e3 (extTrans e2 e1))))

    h5 : allW w5 (λ w6 e6 → (z : w6 ≽ w) → g w6 z (h4 w6 (extTrans e6 e5) z))
    h5 = snd (snd (ig w3 (extTrans e3 (extTrans e2 e1))))




allW-inOpenBar-inOpenBar' : {w : world} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                            → allW w (λ w' e' → (x : f w' e') (at : atOpenBar i w' e' x) → g w' e' x)
                            → inOpenBar' w i g
allW-inOpenBar-inOpenBar' {w} {f} {g} i h w1 e1 =
  w2 ,
  extRefl w2 ,
  λ w3 e3 z → h w3 z (h0 w3 (extTrans e3 (extRefl w2)) z) (ATOPENBAR w1 e1 w3 (extTrans e3 (extRefl (fst (i w1 e1)))) z)
  where
    w2 : world
    w2 = fst (i w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (i w1 e1))

    h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h0 = snd (snd (i w1 e1))



inOpenBar-mon : {w2 w1 : world} {f :  wPred w1} (e : w2 ≽ w1)
                → inOpenBar w1 f
                → inOpenBar w2 (↑wPred f e)
inOpenBar-mon {w2} {w1} {f} e h w' e' = w'' , e'' , h''
  where
    w'' : world
    w'' = fst (h w' (extTrans e' e))

    e'' : w'' ≽ w'
    e'' = fst (snd (h w' (extTrans e' e)))

    h'' : allW w'' (λ w3 e3 → (z : w3 ≽ w2) → ↑wPred f e w3 z)
    h'' w3 e3 z = snd (snd (h w' (extTrans e' e))) w3 e3 (extTrans z e)


allW-inOpenBar : {w : world} {f : wPred w} → allW w f → inOpenBar w f
allW-inOpenBar {w} {f} h w1 e1 =  w1 , extRefl w1 , λ w2 e2 z → h w2 z


inOpenBar-idem : {w : world} {f : wPred w}
                 → inOpenBar w (λ w1 e1 → inOpenBar w1 (↑wPred' f e1))
                 → inOpenBar w f
inOpenBar-idem {w} {f} h w1 e1 =
  fst h4 ,
  extTrans (fst (snd h4)) e2 ,
  λ w3 e3 z → snd (snd h4) w3 e3 (extTrans e3 (fst (snd h4))) z
  where
    w2 : world
    w2 = fst (h w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (h w1 e1))

    h2 : allW w2 (λ w' e' → (z : w' ≽ w) → inOpenBar w' (↑wPred' f z))
    h2 = snd (snd (h w1 e1))

    h3 : inOpenBar w2 (↑wPred' f (extTrans e2 e1))
    h3 = h2 w2 (extRefl w2) (extTrans e2 e1)

    h4 : exAllW w2 (λ w' e' → (z : w' ≽ w2) → (z' : w' ≽ w) → f w' z')
    h4 = h3 w2 (extRefl w2)



inOpenBar-idem2 : {w : world} {f : wPred w}
                  → wPredExtIrr f
                  → inOpenBar w (λ w1 e1 → inOpenBar w1 (↑wPred f e1))
                  → inOpenBar w f
inOpenBar-idem2 {w} {f} ext h w1 e1 =
  fst h4 ,
  extTrans (fst (snd h4)) e2 ,
  h5
  where
    w2 : world
    w2 = fst (h w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (h w1 e1))

    h2 : allW w2 (λ w' e' → (z : w' ≽ w) → inOpenBar w' (↑wPred f z))
    h2 = snd (snd (h w1 e1))

    h3 : inOpenBar w2 (↑wPred f (extTrans e2 e1))
    h3 = h2 w2 (extRefl w2) (extTrans e2 e1)

    h4 : exAllW w2 (λ w' e' → (z : w' ≽ w2) → f w' (extTrans z (extTrans e2 e1)))
    h4 = h3 w2 (extRefl w2)

    h5 : allW (proj₁ h4) (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h5 w3 e3 z = ext w3 _ z (snd (snd h4) w3 e3 (extTrans e3 (fst (snd h4))))



allW-inOpenBar'-inOpenBar-old : {w : world} {f : wPred w} {g : wPredDep f} {h : wPred w}
                                → allW w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                                → (i : inOpenBar w f) → inOpenBar' w i g → inOpenBar w h
allW-inOpenBar'-inOpenBar-old {w} {f} {g} {h} a i q w1 e1 =
  w3 , extTrans e3 e2 , λ w4 e4 z → a w4 z (h0 w4 (extTrans e4 e3) z) (h3 w4 e4 z)
  where
    w2 : world
    w2 = fst (i w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (i w1 e1))

    h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h0 = snd (snd (i w1 e1))

    w3 : world
    w3 = fst (q w1 e1)

    e3 : w3 ≽ w2
    e3 = fst (snd (q w1 e1))

    h3 : allW w3 (λ w4 e4 → (z : w4 ≽ w) → g w4 z (h0 w4 (extTrans e4 e3) z))
    h3 = snd (snd (q w1 e1))



allW-inOpenBar'-inOpenBar : {w : world} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inOpenBar w f)
                            → allW w (λ w' e' → (x : f w' e') → atOpenBar i w' e' x → g w' e' x → h w' e')
                            → inOpenBar' w i g → inOpenBar w h
allW-inOpenBar'-inOpenBar {w} {f} {g} {h} i a q w1 e1 =
  w3 , extTrans e3 e2 , λ w4 e4 z → a w4 z (h0 w4 (extTrans e4 e3) z) (ATOPENBAR w1 e1 w4 (extTrans e4 e3) z) (h3 w4 e4 z)
  where
    w2 : world
    w2 = fst (i w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (i w1 e1))

    h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
    h0 = snd (snd (i w1 e1))

    w3 : world
    w3 = fst (q w1 e1)

    e3 : w3 ≽ w2
    e3 = fst (snd (q w1 e1))

    h3 : allW w3 (λ w4 e4 → (z : w4 ≽ w) → g w4 z (h0 w4 (extTrans e4 e3) z))
    h3 = snd (snd (q w1 e1))



inOpenBar-const : {w : world} {t : Set₁} → inOpenBar w (λ w e → t) → t
inOpenBar-const {w} {t} h = snd (snd (h w (extRefl w))) (fst (h w (extRefl w))) (extRefl _) (fst (snd (h w (extRefl w))))




inOpenBar'-change : {w : world} {f : wPred w} {g : wPredDep f} (i j : inOpenBar w f)
                    → allW w (λ w' e' → (x y : f w' e') → atOpenBar i w' e' x → atOpenBar j w' e' y → g w' e' x → g w' e' y)
                    → inOpenBar' w i g → inOpenBar' w j g
inOpenBar'-change {w} {f} {g} i j aw b w1 e1 =
  w4 , extTrans e4 e3 , h1
  where
    w2 : world
    w2 = fst (j w1 e1)

    e2 : w2 ≽ w1
    e2 = fst (snd (j w1 e1))

    w3 : world
    w3 = fst (i w2 (extTrans e2 e1))

    e3 : w3 ≽ w2
    e3 = fst (snd (i w2 (extTrans e2 e1)))

    w4 : world
    w4 = fst (b w2 (extTrans e2 e1))

    e4 : w4 ≽ w3
    e4 = fst (snd (b w2 (extTrans e2 e1)))

    h0 : allW w4 (λ w5 e5 → (z : w5 ≽ w) → g w5 z (snd (snd (i w2 (extTrans e2 e1))) w5 (extTrans e5 e4) z))
    h0 = snd (snd (b w2 (extTrans e2 e1)))

    h1 : allW w4 (λ w5 e5 → (z : w5 ≽ w) → g w5 z (snd (snd (j w1 e1)) w5 (extTrans e5 (extTrans e4 e3)) z))
    h1 w5 e5 z =
      aw w5 z
         (snd (snd (i w2 (extTrans e2 e1))) w5 (extTrans e5 e4) z)
         (snd (snd (j w1 e1)) w5 (extTrans e5 (extTrans e4 e3)) z)
         (ATOPENBAR w2 (extTrans e2 e1) w5  (extTrans e5 e4) z)
         (ATOPENBAR w1 e1 w5  (extTrans e5 (extTrans e4 e3)) z)
         (h0 w5 e5 z)



-- We can prove that open-bars satisfy the Bar properties
inOpenBar-Bar : Bar
inOpenBar-Bar =
  mkBar
    inOpenBar
    inOpenBar'
    wPredDepExtIrr-inOpenBar
    ↑inOpenBar
    ↑'inOpenBar
--    atOpenBar
    atOpenBar
    inOpenBarFunc
    allW-inOpenBarFunc
    inOpenBar-inOpenBar'
    --(λ {w} {f} {g} {h} → inOpenBar'-inOpenBar' {w} {f} {g} {h})
    allW-inOpenBar-inOpenBar'
    allW-inOpenBar
    inOpenBar-mon
    inOpenBar-idem
    inOpenBar-idem2
    (λ {w} {f} {g} → inOpenBar'-idem {w} {f} {g})
    (λ {w} {f} {g} → inOpenBar'-idem2 {w} {f} {g})
    {--allW-inOpenBar'-inOpenBar--}
    allW-inOpenBar'-inOpenBar
    inOpenBar'-comb
    inOpenBar'-change
    inOpenBar-const
\end{code}
