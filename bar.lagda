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


open import util
open import world
open import choice
-- get rid of worldInstance here and only use world
-- make it a parameter of bar
--open import worldInstance


-- TODO: move the instances to separate files.
-- Choice is only needed for Beth bars to build an infinite sequence of worlds
module bar {L : Level} (W : PossibleWorlds {L}) (C : Choice W) where
open import worldDef{L}(W)
open import choiceDef{L}(W)(C)


record Bar : Set(lsuc(lsuc(L))) where
  constructor mkBar
  field
    -- Operators
    inBar             : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
    inBar'            : (w : 𝕎·) {g : wPred w} (h : inBar w g) (f : wPredDep g) → Set(lsuc(L))
    ↑inBar            : {w : 𝕎·} {f : wPred w} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBar w' (↑wPred f e)
    ↑'inBar           : {w : 𝕎·} {f : wPred w} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBar w' (↑wPred' f e)
    atBar             : {w : 𝕎·} {f : wPred w} (i : inBar w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
    -- Axioms
    atBar-refl        : {w : 𝕎·} {f : wPred w} (i : inBar w f) (p : f w (⊑-refl· w)) → atBar {w} {f} i w (⊑-refl· w) p
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
    inBar-const       : {w : 𝕎·} {t : Set(lsuc(L))} → inBar w (λ w e → t) → t

--    wPredDepExtIrrBar : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : inBar w f) → Set(lsuc(L))
{--    ↑inBar'           : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f) {w' : 𝕎·} (e : w' ⊇ w)
                        → inBar' w i g → inBar' w' (↑inBar i e) (↑wPredDep g e)--}
--    atBar             : {w : 𝕎·} {f : wPred w} (i : inBar w f) (w' : 𝕎·) → Set(lsuc(L))
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


{-----------------------------------------
 --
 -- Open Bar instance
 --
 --}


-- f holds in an open bar
inOpenBar : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
inOpenBar w f =
  ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → ∀𝕎 w2 (λ w3 e3 →
     (z : w ⊑· w3) → f w3 z)))


-- f holds in an open bar that depends on another open bar h
inOpenBar' : (w : 𝕎·) {g : wPred w} (h : inOpenBar w g) (f : wPredDep g) → Set(lsuc(L))
inOpenBar' w h f =
  ∀𝕎 w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           ∃∀𝕎 w1 (λ w2 e2 → (z : w ⊑· w2) → f w2 z (q w2 e2 z)))


wPredDepExtIrr-inOpenBar : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : inOpenBar w f) → Set(lsuc(L))
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




--atOpenBar : {w : 𝕎·} {f : wPred w} (i : inOpenBar w f) (w' : 𝕎·) → Set(lsuc(L))
--atOpenBar {w} {f} i w' = Σ world (λ w1 → Σ (w ⊑· w1) (λ e1 → w' ≽ fst (i w1 e1)))
-- --  Σ (w' ≽ fst (i w1 e1)) (λ e2 → snd (snd (i w1 e1)) w' e2 e)))


data atOpenBar {w : 𝕎·} {f : wPred w} (i : inOpenBar w f) : (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
data atOpenBar {w} {f} i where
  ATOPENBAR-R : (q : f w (⊑-refl· w))
                → atOpenBar {w} {f} i w (⊑-refl· w) q
  ATOPENBAR-O : (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : fst (i w1 e1) ⊑· w2) (z : w ⊑· w2)
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
                   (ATOPENBAR-O w1 (⊑-trans· e e1) w3 (⊑-trans· (proj₁ (snd (j w1 (⊑-trans· e e1)))) e3) (⊑-trans· e z))
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
  λ w3 e3 z → h w3 z (h0 w3 (⊑-trans· (⊑-refl· w2) e3) z) (ATOPENBAR-O w1 e1 w3 (⊑-trans· (⊑-refl· (fst (i w1 e1))) e3) z)
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
  w3 , ⊑-trans· e2 e3 , λ w4 e4 z → a w4 z (h0 w4 (⊑-trans· e3 e4) z) (ATOPENBAR-O w1 e1 w4 (⊑-trans· e3 e4) z) (h3 w4 e4 z)
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



inOpenBar-const : {w : 𝕎·} {t : Set(lsuc(L))} → inOpenBar w (λ w e → t) → t
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
         (ATOPENBAR-O w2 (⊑-trans· e1 e2) w5  (⊑-trans· e4 e5) z)
         (ATOPENBAR-O w1 e1 w5  (⊑-trans· (⊑-trans· e3 e4) e5) z)
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
         (ATOPENBAR-O w2 (⊑-trans· e1 e2) w5 (⊑-trans· e4 e5) z)
         (ATOPENBAR-O w1 e1 w5 (⊑-trans· (⊑-trans· e3 e4) e5) z)
         (h0 w5 e5 z)



-- We can prove that open-bars satisfy the Bar properties
inOpenBar-Bar : Bar
inOpenBar-Bar =
  mkBar
    inOpenBar
    inOpenBar'
    ↑inOpenBar
    ↑'inOpenBar
    atOpenBar
    (λ i → ATOPENBAR-R)
    inOpenBarFunc
    ∀𝕎-inOpenBarFunc
    inOpenBar-inOpenBar'
    ∀𝕎-inOpenBar-inOpenBar'
    ∀𝕎-inOpenBar
    inOpenBar-idem
    (λ {w} {f} {g} → inOpenBar'-idem {w} {f} {g})
    ∀𝕎-inOpenBar'-inOpenBar
    inOpenBar'-comb
    inOpenBar'-change
    inOpenBar-const

--    wPredDepExtIrr-inOpenBar
--    (λ {w} {f} {g} → ↑inOpenBar' {w} {f} {g})
--    atOpenBar
    --(λ {w} {f} {g} {h} → inOpenBar'-inOpenBar' {w} {f} {g} {h})
--    inOpenBar-mon
--    inOpenBar-idem2
--    (λ {w} {f} {g} → inOpenBar'-idem2 {w} {f} {g})
    {--∀𝕎-inOpenBar'-inOpenBar--}
--    old-inOpenBar'-change


{-----------------------------------------
 --
 -- Beth Bar instance -- defined inductively
 --
 -- How will I ever build such a bar??
 --}

-- TODO: would have to disallow equal worlds in indBar-ind
data I𝔹 : 𝕎· → Set(lsuc(L)) where
  indBar-base : (w : 𝕎·) → I𝔹 w
  indBar-ind : (w : 𝕎·) (ind : {w' : 𝕎·} (e : w ⊑· w') → I𝔹 w') → I𝔹 w


inI𝔹 : {w : 𝕎·} (b : I𝔹 w) (f : wPred w) → Set(lsuc(L))
inI𝔹 {w} (indBar-base .w) f = ∀𝕎 w f
inI𝔹 {w} (indBar-ind .w ind) f = {w' : 𝕎·} (e' : w ⊑· w') → inI𝔹 {w'} (ind e') (↑wPred' f e')


inIBethBar : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
inIBethBar w f = Σ (I𝔹 w) (λ b → inI𝔹 b f)


-- TODO: the base case should allow a further bar
inIBethBar' : (w : 𝕎·) {g : wPred w} (h : inIBethBar w g) (f : wPredDep g) → Set(lsuc(L))
inIBethBar' w {g} (indBar-base .w , h) f = ∀𝕎 w (λ w' e' → f w' e' (h w' e'))
inIBethBar' w {g} (indBar-ind .w ind , h) f = {w' : 𝕎·} (e' : w ⊑· w') → inIBethBar' w' (ind e' , h e') (↑wPredDep' f e')


→inI𝔹 : {w : 𝕎·} {f g : wPred w} {b : I𝔹 w}
          → ∀𝕎 w (λ w' e → f w' e → g w' e)
          → inI𝔹 b f
          → inI𝔹 b g
→inI𝔹 {w} {f} {g} {indBar-base .w} aw i w1 e1 = aw w1 e1 (i w1 e1)
→inI𝔹 {w} {f} {g} {indBar-ind .w ind} aw i {w1} e1 =
  →inI𝔹 {w1} {↑wPred' f e1} {↑wPred' g e1} {ind e1} aw' (i e1)
  where
    aw' : ∀𝕎 w1 (λ w'' e → ↑wPred' f e1 w'' e → ↑wPred' g e1 w'' e)
    aw' w2 e2 z x = aw w2 x (z x)


→inI𝔹-↑wPred : {w w' : 𝕎·} (e' : w ⊑· w') (f : wPred w) (b : I𝔹 w') → inI𝔹 b (↑wPred' f e') → inI𝔹 b (↑wPred f e')
→inI𝔹-↑wPred {w} {w'} e' f b i = →inI𝔹 aw i
  where
    aw : ∀𝕎 w' (λ w'' e → ↑wPred' f e' w'' e → ↑wPred f e' w'' e)
    aw w1 e1 z = z (⊑-trans· e' e1)


↑inIBethBar : {w : 𝕎·} {f : wPred w} (i : inIBethBar w f) {w' : 𝕎·} (e : w ⊑· w') → inIBethBar w' (↑wPred f e)
↑inIBethBar {w} {f} (indBar-base .w , i) {w'} e = indBar-base w' , ∀𝕎-mon e i
↑inIBethBar {w} {f} (indBar-ind .w ind , i) {w'} e = ind e , →inI𝔹-↑wPred e f (ind e) (i e)


↑'inIBethBar : {w : 𝕎·} {f : wPred w} (i : inIBethBar w f) {w' : 𝕎·} (e : w ⊑· w') → inIBethBar w' (↑wPred' f e)
↑'inIBethBar {w} {f} (indBar-base .w , i) {w'} e = indBar-base w' , ∀𝕎-mon' e i
↑'inIBethBar {w} {f} (indBar-ind .w ind , i) {w'} e = ind e , i e



↑I𝔹 : {w : 𝕎·} → I𝔹 w → ∀𝕎 w (λ w' _ → I𝔹 w')
↑I𝔹 {w} (indBar-base .w) w' e = indBar-base w'
↑I𝔹 {w} (indBar-ind .w ind) w' e = indBar-ind w' λ {w''} e' → ↑I𝔹 (ind e) w'' e'


→inI𝔹-↑I𝔹 : {w : 𝕎·} {b : I𝔹 w} {f : wPred w}
              → inI𝔹 b f
              → ∀𝕎 w (λ w' e → inI𝔹 (↑I𝔹 b w' e) (↑wPred' f e))
→inI𝔹-↑I𝔹 {w} {indBar-base .w} {f} i w' e' = λ w1 e1 z → i w1 z
→inI𝔹-↑I𝔹 {w} {indBar-ind .w ind} {f} i w' e' {w1} e1 = →inI𝔹-↑I𝔹 (i e') w1 e1


-- it's a composition, not an intersection
∩I𝔹 : {w : 𝕎·} → I𝔹 w → I𝔹 w → I𝔹 w
∩I𝔹 {w} (indBar-base .w) b = b
∩I𝔹 {w} (indBar-ind .w ind) b = indBar-ind w (λ {w'} e → ∩I𝔹 (ind e) (↑I𝔹 b w' e))


∀𝕎-inI𝔹 : {w : 𝕎·} {f g : wPred w} {b : I𝔹 w}
            → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
            → inI𝔹 b f
            → inI𝔹 b g
∀𝕎-inI𝔹 {w} {f} {g} {indBar-base .w} aw i w' e' = aw w' e' (i w' e')
∀𝕎-inI𝔹 {w} {f} {g} {indBar-ind .w ind} aw i {w'} e' =
  ∀𝕎-inI𝔹 {w'} {↑wPred' f e'} {↑wPred' g e'} {ind e'} aw' (i e')
  where
    aw' : ∀𝕎 w' (λ w'' e'' → ↑wPred' f e' w'' e'' → ↑wPred' g e' w'' e'')
    aw' w1 e1 z x = aw w1 x (z x)



inIBethBarFunc-aux : {w : 𝕎·} {f g : wPred w} {b1 b2 : I𝔹 w}
                    → inI𝔹 b1 (λ w' e' → f w' e' → g w' e')
                    → inI𝔹 b2 f
                    → inI𝔹 (∩I𝔹 b1 b2) g
inIBethBarFunc-aux {w} {f} {g} {indBar-base .w} {b2} i j = ∀𝕎-inI𝔹 i j
inIBethBarFunc-aux {w} {f} {g} {indBar-ind .w ind} {b2} i j {w'} e =
  inIBethBarFunc-aux {w'} {↑wPred' f e} {↑wPred' g e} {ind e} {↑I𝔹 b2 w' e} i' j'
  where
    i' : inI𝔹 (ind e) (λ w'' e' → ↑wPred' f e w'' e' → ↑wPred' g e w'' e')
    i' = →inI𝔹 (λ w1 e1 z x u → z u (x u))
                (i e)

    j' : inI𝔹 (↑I𝔹 b2 w' e) (↑wPred' f e)
    j' = →inI𝔹-↑I𝔹 j w' e



inIBethBarFunc : {w : 𝕎·} {f g : wPred w}
                → inIBethBar w (λ w' e' → f w' e' → g w' e')
                → inIBethBar w f → inIBethBar w g
inIBethBarFunc {w} {f} {g} (b1 , i1) (b2 , i2) =
  ∩I𝔹 b1 b2 , inIBethBarFunc-aux i1 i2



∀𝕎-inIBethBarFunc : {w : 𝕎·} {f g : wPred w}
                    → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
                    → inIBethBar w f → inIBethBar w g
∀𝕎-inIBethBarFunc {w} {f} {g} aw (b , i) = (b , →inI𝔹 aw i)



-- inductive type?
data atIBethBar {w : 𝕎·} {f : wPred w} : (i : inIBethBar w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
data atIBethBar {w} {f} where
  ATIBETHBAR-R : (i : inIBethBar w f) (p : f w (⊑-refl· w))
                 → atIBethBar {w} {f} i w (⊑-refl· w) p
  ATIBETHBAR-B : (j : inI𝔹 (indBar-base w) f) (w1 : 𝕎·) (e1 : w ⊑· w1) (p : f w1 e1)
                 → atIBethBar {w} {f} (indBar-base w , j) w1 e1 p
  ATIBETHBAR-I : (ind : {w' : 𝕎·} (e : w ⊑· w') → I𝔹 w')
                 (j : inI𝔹 (indBar-ind w ind) f)
                 (w1 : 𝕎·) (e1 : w ⊑· w1)
                 (w2 : 𝕎·) (e2 : w1 ⊑· w2)
                 (z : w ⊑· w2) (p : ↑wPred' f e1 w2 e2)
                 → atIBethBar {w1} {↑wPred' f e1} (ind e1 , j e1) w2 e2 p
                 → atIBethBar {w} {f} (indBar-ind w ind , j) w2 z (p z)


atIBethBar-refl : {w : 𝕎·} {f : wPred w} (i : inIBethBar w f) (p : f w (⊑-refl· w)) → atIBethBar {w} {f} i w (⊑-refl· w) p
atIBethBar-refl {w} {f} i p = ATIBETHBAR-R i p


{--
inIBethBar-inIBethBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                       → inIBethBar w (λ w' e' → (x : f w' e') → g w' e' x)
                       → (i : inIBethBar w f) → inIBethBar' w i g
inIBethBar-inIBethBar' {w} {f} {g} (b1 , i1) (indBar-base .w , i2) w1 e1 = {!!}
inIBethBar-inIBethBar' {w} {f} {g} (b1 , i1) (indBar-ind .w ind , i2) = {!!}
--}



{-----------------------------------------
 --
 -- Beth Bar instance -- defined from infinite sequences
 --
 --}


-- infinite sequence of worlds
record chain (w : 𝕎·) : Set(lsuc(L)) where
  constructor mkChain
  field
    seq  : ℕ → 𝕎·
    init : w ⊑· seq 0
    prop : (n : ℕ) → seq n ⊏ seq (suc n)


chain⊑n : {w : 𝕎·} (n : ℕ) (c : chain w) → w ⊑· chain.seq c n
chain⊑n {w} 0 c = chain.init c
chain⊑n {w} (suc n) c = ⊑-trans· (chain⊑n n c) (fst (chain.prop c n))


≤→chain⊑ : {w : 𝕎·} {n m : ℕ} (c : chain w) → n ≤ m → chain.seq c n ⊑· chain.seq c m
≤→chain⊑ {w} {.0} {0} c _≤_.z≤n = ⊑-refl· _
≤→chain⊑ {w} {n} {suc m} c h with m≤n⇒m<n∨m≡n h
... | inj₁ p = ⊑-trans· (≤→chain⊑ c (s≤s-inj p)) (fst (chain.prop c m))
... | inj₂ p rewrite p = ⊑-refl· _


record BarsProp (bar : 𝕎· → Set(L)) {w : 𝕎·} (c : chain w) : Set(L) where
  constructor mkBarsProp
  field
    w'  : 𝕎·
    b   : bar w'
    n   : ℕ
    ext : w' ⊑· chain.seq c n


record IS𝔹 (w : 𝕎·) : Set(lsuc(L)) where
  constructor mkIS𝔹
  field
    bar  : 𝕎· → Set(L)
    bars : (c : chain w) → BarsProp bar c
    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    mon  : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2


inIS𝔹 : {w : 𝕎·} (b : IS𝔹 w) (f : wPred w) → Set(lsuc(L))
inIS𝔹 {w} b f = {w' : 𝕎·} (e : w ⊑· w') → IS𝔹.bar b w' → ∀𝕎 w' (↑wPred' f e)


inBethBar : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
inBethBar w f = Σ (IS𝔹 w) (λ b → inIS𝔹 b f)



chain⊑ : {w w' : 𝕎·} (e : w ⊑· w') → chain w' → chain w
chain⊑ {w} {w'} e (mkChain seq init prop) = mkChain seq (⊑-trans· e init) prop


IS𝔹⊑ : {w w' : 𝕎·} (e : w ⊑· w') → IS𝔹 w → IS𝔹 w'
IS𝔹⊑ {w} {w'} e (mkIS𝔹 bar bars ext mon) = mkIS𝔹 bar' bars' ext' mon'
  where
    bar' : 𝕎· → Set(L)
    bar' w0 = Σ 𝕎· (λ w1 → bar w1 × w1 ⊑· w0 × w' ⊑· w0)

    bars' : (c : chain w') → BarsProp bar' c --Σ 𝕎· (λ w'' → bar' w'' × Σ ℕ (λ n → w'' ⊑· chain.seq c n))
    bars' c = mkBarsProp
                (chain.seq (chain⊑ e c) (BarsProp.n z))
                (BarsProp.w' z , BarsProp.b z , BarsProp.ext z , chain⊑n (BarsProp.n z) c)
                (BarsProp.n z)
                (⊑-refl· _)
      where
        z : BarsProp bar (chain⊑ e c) --Σ 𝕎· (λ w'' → bar w'' × Σ ℕ (λ n → w'' ⊑· chain.seq (chain⊑ e c) n))
        z = bars (chain⊑ e c)

    ext' : {w'' : 𝕎·} → bar' w'' → w' ⊑· w''
    ext' {w''} (w1 , b , e₁ , e₂) = e₂

    mon' : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar' w1 → bar' w2
    mon' {w1} {w2} e (w0 , b0 , e₁ , e₂) = w0 , b0 , ⊑-trans· e₁ e , ⊑-trans· e₂ e


↑inBethBar : {w : 𝕎·} {f : wPred w} (i : inBethBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBethBar w' (↑wPred f e)
↑inBethBar {w} {f} (b , i) {w'} e = IS𝔹⊑ e b , j
  where
    j : inIS𝔹 (IS𝔹⊑ e b) (↑wPred f e)
    j {w1} e1 (w0 , b0 , e₁ , e₂) w2 e2 z = i (IS𝔹.ext b {w0} b0) b0 w2 (⊑-trans· e₁ e2) (⊑-trans· e z)


↑'inBethBar : {w : 𝕎·} {f : wPred w} (i : inBethBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBethBar w' (↑wPred' f e)
↑'inBethBar {w} {f} (b , i) {w'} e = IS𝔹⊑ e b , j
  where
    j : inIS𝔹 (IS𝔹⊑ e b) (↑wPred' f e)
    j {w1} e1 (w0 , b0 , e₁ , e₂) w2 e2 z x = i (IS𝔹.ext b {w0} b0) b0 w2 (⊑-trans· e₁ e2) x


∩IS𝔹 : {w : 𝕎·} → IS𝔹 w → IS𝔹 w → IS𝔹 w
∩IS𝔹 {w} (mkIS𝔹 b1 bars1 ext1 mon1) (mkIS𝔹 b2 bars2 ext2 mon2) =
  mkIS𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set(L)
    bar w0 = Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → b1 w1 × b2 w2 × w1 ⊑· w0 × w2 ⊑· w0))

    bars : (c : chain w) → BarsProp bar c --Σ 𝕎· (λ w' → bar w' × Σ ℕ (λ n → w' ⊑· chain.seq c n))
    bars c = mkBarsProp (chain.seq c ((BarsProp.n z1) ⊔ (BarsProp.n z2)))
                        (BarsProp.w' z1 , BarsProp.w' z2 , BarsProp.b z1 , BarsProp.b z2 , e1 , e2)
                        ((BarsProp.n z1) ⊔ (BarsProp.n z2))
                        (⊑-refl· _)
      where
        z1 : BarsProp b1 c --Σ 𝕎· (λ w' → b1 w' × Σ ℕ (λ n → w' ⊑· chain.seq c n))
        z1 = bars1 c

        z2 : BarsProp b2 c --Σ 𝕎· (λ w' → b2 w' × Σ ℕ (λ n → w' ⊑· chain.seq c n))
        z2 = bars2 c

        e1 : BarsProp.w' z1 ⊑· chain.seq c (BarsProp.n z1 ⊔ BarsProp.n z2)
        e1 = ⊑-trans· (BarsProp.ext z1) (≤→chain⊑ c (m≤m⊔n (BarsProp.n z1) (BarsProp.n z2)))

        e2 : BarsProp.w' z2 ⊑· chain.seq c (BarsProp.n z1 ⊔ BarsProp.n z2)
        e2 = ⊑-trans· (BarsProp.ext z2) (≤→chain⊑ c (m≤n⊔m (BarsProp.n z1) (BarsProp.n z2)))

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (w1 , w2 , b₁ , b₂ , e₁ , e₂) = ⊑-trans· (IS𝔹.ext (mkIS𝔹 b1 bars1 ext1 mon1) {w1} b₁) e₁

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (wa , wb , ba , bb , ea , eb) = wa , wb , ba , bb , ⊑-trans· ea e , ⊑-trans· eb e



inBethBarFunc : {w : 𝕎·} {f g : wPred w}
                → inBethBar w (λ w' e' → f w' e' → g w' e')
                → inBethBar w f → inBethBar w g
inBethBarFunc {w} {f} {g} (b1 , i1) (b2 , i2) =
  ∩IS𝔹 b1 b2 , i
  where
    i : inIS𝔹 (∩IS𝔹 b1 b2) g
    i e (w₁ , w₂ , b₁ , b₂ , e₁ , e₂) w' e' z =
      i1 (IS𝔹.ext b1 b₁) b₁ w' (⊑-trans· e₁ e') z
         (i2 (IS𝔹.ext b2 b₂) b₂ w' (⊑-trans· e₂ e') z)


∀𝕎-inBethBarFunc : {w : 𝕎·} {f g : wPred w}
                    → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
                    → inBethBar w f → inBethBar w g
∀𝕎-inBethBarFunc {w} {f} {g} aw (b , i) = b , j
  where
    j : inIS𝔹 b g
    j e b' w' e' z = aw w' z (i (IS𝔹.ext b b') b' w' e' z)



inIS𝔹Dep : {w : 𝕎·} (b : IS𝔹 w) {f : wPred w} (g : wPredDep f) → Set(lsuc(L))
inIS𝔹Dep {w} b {f} g =
  {w' : 𝕎·} (e : w ⊑· w') → IS𝔹.bar b w' → ∀𝕎 w' (λ w'' e' → (x : w ⊑· w'') (y : f w'' x) → g w'' x y)


inBethBar' : (w : 𝕎·) {g : wPred w} (h : inBethBar w g) (f : wPredDep g) → Set(lsuc(L))
inBethBar' w {g} (b , i) f =
  {w' : 𝕎·} (e : w ⊑· w') (ib : IS𝔹.bar b w')
  → Σ (IS𝔹 w') (λ b' → inIS𝔹Dep b' (↑wPredDep' f e))
--∀𝕎 w' (λ w'' e' → (z : w ⊑· w'') → f w'' z (i e ib w'' e' z))


inBethBar-inBethBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                       → inBethBar w (λ w' e' → (x : f w' e') → g w' e' x)
                       → (i : inBethBar w f) → inBethBar' w i g
inBethBar-inBethBar' {w} {f} {g} (b1 , i1) (b2 , i2) {w'} e ib =
  IS𝔹⊑ e b1 , j
  where
    j : inIS𝔹Dep (IS𝔹⊑ e b1) (↑wPredDep' g e)
    j {w0} e0 (w0' , b0 , e0' , e0'') w1 e1 x y x' y' = i1 (IS𝔹.ext b1 b0) b0 w1 (⊑-trans· e0' e1) x' y'


trivialIS𝔹 : (w : 𝕎·) → IS𝔹 w
trivialIS𝔹 w =
  mkIS𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set(L)
    bar w' = w ⊑· w'

    bars : (c : chain w) → BarsProp bar c
    bars c = mkBarsProp w (⊑-refl· _) 0 (chain.init c)

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} b = b

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e b = ⊑-trans· b e


∀𝕎-inBethBar : {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → inBethBar w f
∀𝕎-inBethBar {w} {f} h = trivialIS𝔹 w , i
  where
    i : inIS𝔹 (trivialIS𝔹 w) f
    i {w'} e b w1 e1 z = h w1 z


seqChoice : 𝕎· → ℕ → 𝕎·
seqChoice w 0 = w
seqChoice w (suc n) = startNewChoice (seqChoice w n)


-- creates a chain by starting new choices at each step
chainChoice : (w : 𝕎·) → chain w
chainChoice w = mkChain (seqChoice w) (⊑-refl· _) p
  where
    p : (n : ℕ) → seqChoice w n ⊏ startNewChoice (seqChoice w n)
    p n = startNewChoice⊏· (seqChoice w n)


inBethBar-const : {w : 𝕎·} {t : Set(lsuc(L))} → inBethBar w (λ w e → t) → t
inBethBar-const {w} {t} (b , i) = z _ (⊑-refl· _) (IS𝔹.ext b (BarsProp.b bp))
  where
    bp : BarsProp (IS𝔹.bar b) (chainChoice w)
    bp = IS𝔹.bars b (chainChoice w)

    z : ∀𝕎 (BarsProp.w' bp) (↑wPred' (λ _ _ → t) (IS𝔹.ext b (BarsProp.b bp)))
    z = i (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp)


data atBethBar {w : 𝕎·} {f : wPred w} (i : inBethBar w f) : (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
data atBethBar {w} {f} i where
  ATBETHBAR-R :  (p : f w (⊑-refl· w))
                → atBethBar {w} {f} i w (⊑-refl· w) p
  ATBETHBAR-B : (w1 : 𝕎·) (e1 : w ⊑· w1) (b : IS𝔹.bar (fst i) w1)
                (w2 : 𝕎·) (e2 : w1 ⊑· w2) (z : w ⊑· w2)
                (p : f w2 z)
                → atBethBar {w} {f} i w2 z p --(snd i e1 b w2 e2 z)


atBethBar-refl : {w : 𝕎·} {f : wPred w} (i : inBethBar w f) (p : f w (⊑-refl· w)) → atBethBar {w} {f} i w (⊑-refl· w) p
atBethBar-refl {w} {f} i p = ATBETHBAR-R p



∀𝕎-inBethBar-inBethBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBethBar w f)
                           → ∀𝕎 w (λ w' e' → (x : f w' e') (at : atBethBar i w' e' x) → g w' e' x)
                           → inBethBar' w i g
∀𝕎-inBethBar-inBethBar' {w} {f} {g} (b , i) aw {w'} e ib =
  trivialIS𝔹 w' , j
  where
    j : inIS𝔹Dep (trivialIS𝔹 w') (↑wPredDep' g e)
    j {w0} e0 ib' w1 e1 x y x' y' = aw w1 x' y' at
      where
        at : atBethBar (b , i) w1 x' y'
        at = ATBETHBAR-B w' e ib w1 x x' y'


record IS𝔹Fam {w : 𝕎·} (b : IS𝔹 w) : Set(L) where
  constructor mkIS𝔹Fam
  field
    w1 : 𝕎·
    e1 : w ⊑· w1
    br : IS𝔹.bar b w1
    w2 : 𝕎·
    e2 : w1 ⊑· w2
    z  : w ⊑· w2


truncateChain : {w : 𝕎·} {c : chain w} {n : ℕ} {w' : 𝕎·} (e : w' ⊑· chain.seq c n) → chain w'
truncateChain {w} {c} {n} {w'} e = mkChain (λ x → chain.seq c (x + n)) e p
  where
    p : (x : ℕ) → chain.seq c (x + n) ⊏ chain.seq c (suc (x + n))
    p x = chain.prop c (x + n)



{--
IS𝔹-fam : {w : 𝕎·} {f : wPred w} (b : IS𝔹 w) (i : inIS𝔹 b (λ w' e' → inBethBar w' (↑wPred' f e'))) → IS𝔹 w
IS𝔹-fam {w} {f} b i = mkIS𝔹 bar bars ext
  where
    bar : 𝕎· → Set(L)
    bar w' = Σ (IS𝔹Fam b) (λ F → IS𝔹.bar (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) w')

    bars : (c : chain w) → BarsProp bar c
    bars c = mkBarsProp (BarsProp.w' bp') br (BarsProp.n bp' + BarsProp.n bp) e
      where
        bp : BarsProp (IS𝔹.bar b) c
        bp = IS𝔹.bars b c

        b' : IS𝔹 (BarsProp.w' bp)
        b' = fst (i (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp) (BarsProp.w' bp) (⊑-refl· _) (IS𝔹.ext b (BarsProp.b bp)))

        bp' : BarsProp (IS𝔹.bar b') (truncateChain {w} {c} {BarsProp.n bp} {BarsProp.w' bp} (BarsProp.ext bp))
        bp' = IS𝔹.bars b' (truncateChain {w} {c} {BarsProp.n bp} {BarsProp.w' bp} (BarsProp.ext bp))

        br : bar (BarsProp.w' bp')
        br = mkIS𝔹Fam (BarsProp.w' bp) (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp) (BarsProp.w' bp) (⊑-refl· _) (IS𝔹.ext b (BarsProp.b bp)) ,
             BarsProp.b bp'

        e : BarsProp.w' bp' ⊑· chain.seq c (BarsProp.n bp' + BarsProp.n (IS𝔹.bars b c))
        e = BarsProp.ext bp'

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (IS𝔹Fam.z F) (IS𝔹.ext (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) b')
--}


IS𝔹-fam : {w : 𝕎·} (b : IS𝔹 w)
           (G : {w0 : 𝕎·} (e0 : w ⊑· w0) {w1 : 𝕎·} (e1 : w0 ⊑· w1) (z : w ⊑· w1) → IS𝔹 w1 → Set(lsuc(L)))
           (i : {w0 : 𝕎·} (e0 : w ⊑· w0) (ib0 : IS𝔹.bar b w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w ⊑· w1)
                → Σ (IS𝔹 w1) (λ b' → G e0 e1 z b'))
           → IS𝔹 w
IS𝔹-fam {w} b G i = mkIS𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set(L)
    bar w' = Σ (IS𝔹Fam b) (λ F → IS𝔹.bar (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) w')

    bars : (c : chain w) → BarsProp bar c
    bars c = mkBarsProp (BarsProp.w' bp') br (BarsProp.n bp' + BarsProp.n bp) e
      where
        bp : BarsProp (IS𝔹.bar b) c
        bp = IS𝔹.bars b c

        b' : IS𝔹 (BarsProp.w' bp)
        b' = fst (i (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp) (BarsProp.w' bp) (⊑-refl· _) (IS𝔹.ext b (BarsProp.b bp)))

        bp' : BarsProp (IS𝔹.bar b') (truncateChain {w} {c} {BarsProp.n bp} {BarsProp.w' bp} (BarsProp.ext bp))
        bp' = IS𝔹.bars b' (truncateChain {w} {c} {BarsProp.n bp} {BarsProp.w' bp} (BarsProp.ext bp))

        br : bar (BarsProp.w' bp')
        br = mkIS𝔹Fam (BarsProp.w' bp) (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp) (BarsProp.w' bp) (⊑-refl· _) (IS𝔹.ext b (BarsProp.b bp)) ,
             BarsProp.b bp'

        e : BarsProp.w' bp' ⊑· chain.seq c (BarsProp.n bp' + BarsProp.n (IS𝔹.bars b c))
        e = BarsProp.ext bp'

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (IS𝔹Fam.z F) (IS𝔹.ext (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) b')

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (F , b) = F , IS𝔹.mon (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) e b



inBethBar-idem : {w : 𝕎·} {f : wPred w}
                 → inBethBar w (λ w' e' → inBethBar w' (↑wPred' f e'))
                 → inBethBar w f
inBethBar-idem {w} {f} (b , i) =
  IS𝔹-fam {w} b (λ w1 e1 z b' → inIS𝔹 b' (↑wPred' f z)) i , j
  where
    j : inIS𝔹 (IS𝔹-fam {w} b (λ w1 e1 z b' → inIS𝔹 b' (↑wPred' f z)) i) f
    j {w'} e (mkIS𝔹Fam w2 e2 br₁ w3 e3 z₁ , br) w1 e1 z =
      snd (i e2 br₁ w3 e3 z₁)
          (IS𝔹.ext (proj₁ (i e2 br₁ w3 e3 z₁)) br)
          br w1 e1 (⊑-trans· (IS𝔹.ext (proj₁ (i e2 br₁ w3 e3 z₁)) br) e1) z




record IS𝔹In {w : 𝕎·} (b : IS𝔹 w) : Set(L) where
  constructor mkIS𝔹In
  field
    w1 : 𝕎·
    e1 : w ⊑· w1
    br : IS𝔹.bar b w1


IS𝔹-fam2 : {w : 𝕎·} (b : IS𝔹 w)
            (G : {w' : 𝕎·} (e : w ⊑· w') → IS𝔹 w' → Set(lsuc(L)))
            (i : {w' : 𝕎·} (e : w ⊑· w') → IS𝔹.bar b w' → Σ (IS𝔹 w') (λ b' → G e b'))
            → IS𝔹 w
IS𝔹-fam2 {w} b G i = mkIS𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set(L)
    bar w' = Σ (IS𝔹In b) (λ F → IS𝔹.bar (fst (i (IS𝔹In.e1 F) (IS𝔹In.br F))) w')

    bars : (c : chain w) → BarsProp bar c
    bars c = mkBarsProp (BarsProp.w' bp') br (BarsProp.n bp' + BarsProp.n bp) e
      where
        bp : BarsProp (IS𝔹.bar b) c
        bp = IS𝔹.bars b c

        b' : IS𝔹 (BarsProp.w' bp)
        b' = fst (i (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp))

        bp' : BarsProp (IS𝔹.bar b') (truncateChain {w} {c} {BarsProp.n bp} {BarsProp.w' bp} (BarsProp.ext bp))
        bp' = IS𝔹.bars b' (truncateChain {w} {c} {BarsProp.n bp} {BarsProp.w' bp} (BarsProp.ext bp))

        br : bar (BarsProp.w' bp')
        br = mkIS𝔹In (BarsProp.w' bp) (IS𝔹.ext b (BarsProp.b bp)) (BarsProp.b bp) ,
             BarsProp.b bp'

        e : BarsProp.w' bp' ⊑· chain.seq c (BarsProp.n bp' + BarsProp.n (IS𝔹.bars b c))
        e = BarsProp.ext bp'

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (IS𝔹In.e1 F) (IS𝔹.ext (fst (i (IS𝔹In.e1 F) (IS𝔹In.br F))) b')

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (F , b) = F , IS𝔹.mon (fst (i (IS𝔹In.e1 F) (IS𝔹In.br F))) e b



∀𝕎-inBethBar'-inBethBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inBethBar w f)
                           → ∀𝕎 w (λ w' e' → (x : f w' e') → atBethBar i w' e' x → g w' e' x → h w' e')
                           → inBethBar' w i g → inBethBar w h
∀𝕎-inBethBar'-inBethBar {w} {f} {g} {h} (b , i) aw j =
  IS𝔹-fam2 {w} b (λ {w'} e b' → inIS𝔹Dep b' (↑wPredDep' g e)) j , i'
  where
    i' : inIS𝔹 (IS𝔹-fam2 {w} b (λ {w'} e b' → inIS𝔹Dep b' (↑wPredDep' g e)) j) h
    i' {w'} e (mkIS𝔹In w2 e2 br , F) w1 e1 z =
      aw w1 z
         (i e2 br w1 (⊑-trans· (IS𝔹.ext (proj₁ (j e2 br)) F) e1) z)
         (ATBETHBAR-B w2 e2 br w1 (⊑-trans· (IS𝔹.ext (proj₁ (j e2 br)) F) e1) z
                      (i e2 br w1 (⊑-trans· (IS𝔹.ext (proj₁ (j e2 br)) F) e1) z))
         (snd (j e2 br)
              (IS𝔹.ext (proj₁ (j e2 br)) F)
              F w1 e1
              (⊑-trans· (IS𝔹.ext (proj₁ (j e2 br)) F) e1)
              (i e2 br w1 (⊑-trans· (IS𝔹.ext (proj₁ (j e2 br)) F) e1))
              z
              (i e2 br w1 (⊑-trans· (IS𝔹.ext (proj₁ (j e2 br)) F) e1) z))



inBethBar'-comb : {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : inBethBar w f)
                  → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                                   → g w' e' zg → h w' e' zh → k w' e' z)
                  → inBethBar' w i g → inBethBar' w i h → inBethBar' w i k
inBethBar'-comb {w} {f} {g} {h} {k} i aw j₁ j₂ {w'} e ib =
  ∩IS𝔹 b1 b2 , j
  where
    b1 : IS𝔹 w'
    b1 = fst (j₁ e ib)

    i1 : inIS𝔹Dep b1 (↑wPredDep' g e)
    i1 = snd (j₁ e ib)

    b2 : IS𝔹 w'
    b2 = fst (j₂ e ib)

    i2 : inIS𝔹Dep b2 (↑wPredDep' h e)
    i2 = snd (j₂ e ib)

    j : inIS𝔹Dep (∩IS𝔹 b1 b2) (↑wPredDep' k e)
    j {w0} e0 (wa , wb , ba , bb , ea , eb) w1 e1 x y x' y' =
      aw w1 x' y' y' y'
         (i1 (IS𝔹.ext b1 ba) ba w1 (⊑-trans· ea e1) x y x' y')
         (i2 (IS𝔹.ext b2 bb) bb w1 (⊑-trans· eb e1) x y x' y')




inBethBar'-idem : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBethBar w f)
                  → inBethBar w (λ w' e' → inBethBar' w' (↑'inBethBar i e') (↑wPredDep' g e'))
                  → inBethBar' w i g
inBethBar'-idem {w} {f} {g} (b₁ , i) (b₂ , j) {w'} e ib =
  IS𝔹-fam {w'} (IS𝔹⊑ e b₂) (λ {w0} e0 {w1} e1 z b' → inIS𝔹Dep b' (↑wPredDep' (↑wPredDep' g (⊑-trans· e e0)) e1)) j' ,
  jd
  where
    j' : {w0 : 𝕎·} (e0 : w' ⊑· w0) (ib0 : IS𝔹.bar (IS𝔹⊑ e b₂) w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w' ⊑· w1)
         → Σ (IS𝔹 w1) (λ b' → inIS𝔹Dep b' (↑wPredDep' (↑wPredDep' g (⊑-trans· e e0)) e1))
    j' {w0} e0 (wa , ba , ea₁ , ea₂) w1 e1 z =
      j (IS𝔹.ext b₂ ba) ba w0 ea₁ (⊑-trans· e e0) e1 (w' , ib , ⊑-trans· e0 e1 , e1)

    jd : inIS𝔹Dep (IS𝔹-fam (IS𝔹⊑ e b₂) (λ {w0} e0 {w1} e1 z b' → inIS𝔹Dep b' (↑wPredDep' (↑wPredDep' g (⊑-trans· e e0)) e1)) j')
                   (↑wPredDep' g e)
    jd {w0} e0 (mkIS𝔹Fam w2 e2 br w3 e3 z , b0) w1 e1 x y x' y' =
      snd (j' e2 br w3 e3 z)
          (IS𝔹.ext (fst (j' e2 br w3 e3 z)) b0)
          b0 w1 e1
          (⊑-trans· (IS𝔹.ext (fst (j' e2 br w3 e3 z)) b0) e1)
          (i (⊑-trans· (IS𝔹.ext b₁ ib) e2) (IS𝔹.mon b₁ e2 ib) w1)
          (⊑-trans· e3 (⊑-trans· (IS𝔹.ext (fst (j' e2 br w3 e3 z)) b0) e1))
          y x' y'



inBethBar'-change : {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k}
                    (i : inBethBar w f) (j : inBethBar w k)
                    → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e') → atBethBar i w' e' x → atBethBar j w' e' y
                                     → g w' e' x → h w' e' y)
                    → inBethBar' w i g → inBethBar' w j h
inBethBar'-change {w} {f} {k} {g} {h} (b₁ , i) (b₂ , j) aw z {w'} e ib =
  IS𝔹-fam2 (IS𝔹⊑ e b₁) (λ {w0} e0 b' → inIS𝔹Dep b' (↑wPredDep' g (⊑-trans· e e0))) z' , jd
  where
    z' : {w0 : 𝕎·} (e0 : w' ⊑· w0) (ib0 : IS𝔹.bar (IS𝔹⊑ e b₁) w0)
          → Σ (IS𝔹 w0) (λ b' → inIS𝔹Dep b' (↑wPredDep' g (⊑-trans· e e0)))
    z' {w0} e0 (wa , ba , ea₁ , ea₂) = z (⊑-trans· e ea₂) (IS𝔹.mon b₁ ea₁ ba)

    jd : inIS𝔹Dep (IS𝔹-fam2 (IS𝔹⊑ e b₁) (λ {w0} e0 b' → inIS𝔹Dep b' (↑wPredDep' g (PossibleWorlds.⊑-trans W e e0))) z')
                   (↑wPredDep' h e)
    jd {w0} e0 (mkIS𝔹In w2 e2 (w3 , br , e3 , e4) , b0) w1 e1 x y x' y' =
      aw w1 x'
         (i (IS𝔹.ext b₁ br) br
            w1
            (⊑-trans· e3 (⊑-trans· (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1))
            x')
         y'
         (ATBETHBAR-B w3 (IS𝔹.ext b₁ br) br w1
                      (⊑-trans· e3 (⊑-trans· (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1))
                      x' (i (IS𝔹.ext b₁ br) br w1
                      (⊑-trans· e3 (⊑-trans· (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1))
                      x'))
         (ATBETHBAR-B w' e ib w1 x x' y')
         (snd (z' e2 (w3 , br , e3 , e4))
              (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0)
              b0 w1 e1
              (⊑-trans· (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1)
              (i (IS𝔹.ext b₁ br) br w1 (⊑-trans· e3 (⊑-trans· (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1)))
              x'
              (i (IS𝔹.ext b₁ br) br w1 (⊑-trans· e3 (⊑-trans· (IS𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1)) x'))



inBethBar-Bar : Bar
inBethBar-Bar =
  mkBar
    inBethBar
    inBethBar'
    ↑inBethBar
    ↑'inBethBar
    atBethBar
    atBethBar-refl
    inBethBarFunc
    ∀𝕎-inBethBarFunc
    inBethBar-inBethBar'
    ∀𝕎-inBethBar-inBethBar'
    ∀𝕎-inBethBar
    inBethBar-idem
    inBethBar'-idem
    ∀𝕎-inBethBar'-inBethBar
    inBethBar'-comb
    inBethBar'-change
    inBethBar-const

\end{code}
