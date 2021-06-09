\begin{code}
open import Agda.Builtin.Sigma
open import world

module bar where

record Bar : Set₂ where
  constructor mkBar
  field
    inBar     : (w : world) (f : wPred w) → Set₁
    inBar'    : (w : world) {g : wPred w} (h : inBar w g) (f : ∀ w' (e : w' ≽ w) (x : g w' e) → Set₁) → Set₁
    inBarFunc : (w : world) (f g : wPred w) → wPredExtIrr f → wPredExtIrr g → inBar w (λ w' e' → f w' e' → g w' e') → inBar w f → inBar w g

inOpenBarFunc : (w : world) (f g : wPred w) → wPredExtIrr f → wPredExtIrr g → inOpenBar w (λ w' e' → f w' e' → g w' e') → inOpenBar w f → inOpenBar w g
inOpenBarFunc w f g if ig F h w1 e1 =
  (fst h2 , extTrans (fst (snd h2)) e2 , h3)
  where
    h1 : exAllW w1 λ w2 e2 → f w2 (extTrans e2 e1)
    h1 = h w1 e1

    w2 : world
    w2 = fst h1

    e2 : w2 ≽ w1
    e2 = fst (snd h1)

    h2 : exAllW w2 (λ w' e' → f w' (extTrans e' (extTrans e2 e1)) → g w' (extTrans e' (extTrans e2 e1)))
    h2 = F w2 (extTrans e2 e1)

    w3 : world
    w3 = fst h2

    e3 : w3 ≽ w2
    e3 = fst (snd h2)

    h3 : allW w3 (λ w4 e4 → g w4 (extTrans (extTrans e4 (extTrans e3 e2)) e1))
    h3 w4 e4 =
      ig w4
         (extTrans (extTrans e4 e3) (extTrans e2 e1))
         (extTrans (extTrans e4 (extTrans e3 e2)) e1)
         (h4 (if w4 (extTrans (extTrans (extTrans e4 e3) e2) e1) (extTrans (extTrans e4 e3) (extTrans e2 e1)) h5))
      where
        h4 : f w4 (extTrans (extTrans e4 e3) (extTrans e2 e1)) → g w4 (extTrans (extTrans e4 e3) (extTrans e2 e1))
        h4 = snd (snd h2) w4 e4

        h5 : f w4 (extTrans (extTrans (extTrans e4 e3) e2) e1)
        h5 = snd (snd h1) w4 (extTrans e4 e3)

-- We can prove that open-bars satisfy the Bar properties
inOpenBar-Bar : Bar
inOpenBar-Bar = mkBar inOpenBar inOpenBar' inOpenBarFunc
\end{code}
