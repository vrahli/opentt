\begin{code}
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import world

module bar where

record Bar : Set₂ where
  constructor mkBar
  field
    inBar             : (w : world) (f : wPred w) → Set₁
    inBar'            : (w : world) {g : wPred w} (h : inBar w g) (f : wPredDep g) → Set₁
    inBarFunc         : {w : world} {f g : wPred w}
                        → inBar w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    allW-inBarFunc    : {w : world} {f g : wPred w}
                        → allW w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    inBar-inBar'      : {w : world} {f : wPred w} {g : wPredDep f}
                        → inBar w (λ w' e' → (x : f w' e') → g w' e' x)
                        → (i : inBar w f) → inBar' w i g
    allW-inBar-inBar' : {w : world} {f : wPred w} {g : wPredDep f}
                        → allW w (λ w' e' → (x : f w' e') → g w' e' x)
                        → (i : inBar w f) → inBar' w i g
    allW-inBar        : {w : world} {f : wPred w} → allW w f → inBar w f
    inBar-mon         : {w2 w1 : world} {f : wPred w1} (e : w2 ≽ w1)
                        → inBar w1 f → inBar w2 (↑wPred f e)
    inBar-idem        : {w : world} {f : wPred w}
                        → wPredExtIrr f
                        → inBar w (λ w' e' → inBar w' (↑wPred f e'))
                        → inBar w f
    allW-inBar'-inBar : {w : world} {f : wPred w} {g : wPredDep f} {h : wPred w}
                        → allW w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                        → (i : inBar w f) → inBar' w i g → inBar w h
    inBar-const       : {w : world} {t : Set₁} → inBar w (λ w e → t) → t


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
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 →
             (z : w3 ≽ w) → f w3 z (q w3 (extTrans e3 e2) z))))

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


allW-inOpenBar-inOpenBar' : {w : world} {f : wPred w} {g : wPredDep f}
                            → allW w (λ w' e' → (x : f w' e') → g w' e' x)
                            → (i : inOpenBar w f) → inOpenBar' w i g
allW-inOpenBar-inOpenBar' {w} {f} {g} h i w1 e1 = w2 , extRefl w2 , λ w3 e3 z → h w3 z (h0 w3 (extTrans e3 (extRefl w2)) z)
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
                 → wPredExtIrr f
                 → inOpenBar w (λ w' e' → inOpenBar w' (↑wPred f e'))
                 → inOpenBar w f
inOpenBar-idem {w} {f} ei h w1 e1 =
  fst h4 ,
  extTrans (fst (snd h4)) e2 ,
  λ w3 e3 z → ei w3 (extTrans (extTrans e3 (fst (snd h4))) (extTrans e2 e1)) z (snd (snd h4) w3 e3 (extTrans e3 (fst (snd h4))))
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


allW-inOpenBar'-inOpenBar : {w : world} {f : wPred w} {g : wPredDep f} {h : wPred w}
                            → allW w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                            → (i : inOpenBar w f) → inOpenBar' w i g → inOpenBar w h
allW-inOpenBar'-inOpenBar {w} {f} {g} {h} a i q w1 e1 =
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


inOpenBar-const : {w : world} {t : Set₁} → inOpenBar w (λ w e → t) → t
inOpenBar-const {w} {t} h = snd (snd (h w (extRefl w))) (fst (h w (extRefl w))) (extRefl _) (fst (snd (h w (extRefl w))))


-- We can prove that open-bars satisfy the Bar properties
inOpenBar-Bar : Bar
inOpenBar-Bar =
  mkBar
    inOpenBar
    inOpenBar'
    inOpenBarFunc
    allW-inOpenBarFunc
    inOpenBar-inOpenBar'
    allW-inOpenBar-inOpenBar'
    allW-inOpenBar
    inOpenBar-mon
    inOpenBar-idem
    allW-inOpenBar'-inOpenBar
    inOpenBar-const
\end{code}
