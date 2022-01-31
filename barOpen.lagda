\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; pred ; _⊔_)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Empty


open import util
open import calculus
open import world


module barOpen {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)
open import bar(W)



{-----------------------------------------
 --
 -- Open Bar instance
 --
 --}

------
-- An open bar
O𝔹bars : Bars
O𝔹bars w bar = ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 _ → Lift (lsuc(L)) (bar w2)))


O𝔹bars⊑ : Bars⊑ O𝔹bars
O𝔹bars⊑ {w1} {w2} e bar h w3 e3 =
  fst (h w3 (⊑-trans· e e3)) ,
  fst (snd (h w3 (⊑-trans· e e3))) ,
  lift (fst (h w3 (⊑-trans· e e3)) ,
        lower (snd (snd (h w3 (⊑-trans· e e3)))) ,
        ⊑-refl· _ ,
        ⊑-trans· e3 (fst (snd (h w3 (⊑-trans· e e3)))))


O𝔹bars∩ : Bars∩ O𝔹bars
O𝔹bars∩ {w} b1 b2 bars1 bars2 w1 e1 =
  fst h2 ,
  ⊑-trans· (fst (snd h1)) (fst (snd h2)) ,
  lift (fst h1 , fst h2 , lower (snd (snd h1)) , lower (snd (snd h2)) , fst (snd h2) , ⊑-refl· _)
  where
    h1 : ∃𝕎 w1 (λ w2 e2 → Lift (lsuc L) (b1 w2))
    h1 = bars1 w1 e1

    h2 : ∃𝕎 (fst h1) (λ w2 e2 → Lift (lsuc L) (b2 w2))
    h2 = bars2 (fst h1) (⊑-trans· e1 (fst (snd h1)))


O𝔹bars∀ : Bars∀ O𝔹bars
O𝔹bars∀ w w1 e1 = w1 , ⊑-refl· _ , lift e1


{--O𝔹barsFam1 : BarsFam1 O𝔹bars
O𝔹barsFam1 {w} b G i w1 e1 =
  fst (𝔹.bars b' (𝔹Fam.w2 bf) (⊑-refl· _)) ,
  ⊑-trans· (fst (snd (𝔹.bars b w1 e1))) (𝔹.ext b' (lower (snd (snd (𝔹.bars b' (𝔹Fam.w2 bf) (⊑-refl· _)))))) ,
  lift (bf , lower (snd (snd (𝔹.bars b' (𝔹Fam.w2 bf) (⊑-refl· _)))))
  where
    bf : 𝔹Fam b
    bf = mk𝔹Fam (fst (𝔹.bars b w1 e1))
                 (⊑-trans· e1 (fst (snd (𝔹.bars b w1 e1))))
                 (lower (snd (snd (𝔹.bars b w1 e1))))
                 (fst (𝔹.bars b w1 e1))
                 (⊑-refl· _)
                 (⊑-trans· e1 (fst (snd (𝔹.bars b w1 e1))))

    b' : 𝔹 O𝔹bars (fst (𝔹.bars b w1 e1))
    b' = fst (i (𝔹Fam.e1 bf) (𝔹Fam.br bf) (𝔹Fam.w2 bf) (𝔹Fam.e2 bf) (𝔹Fam.z bf))
--}


O𝔹barsFam2 : BarsFam2 O𝔹bars
O𝔹barsFam2 {w} b G i w1 e1 =
  fst (𝔹.bars b' (𝔹In.w1 bi) (⊑-refl· _)) ,
  ⊑-trans· (fst (snd (𝔹.bars b w1 e1))) (fst (snd (𝔹.bars b' (𝔹In.w1 bi) (⊑-refl· _)))) ,
  lift (bi , lower (snd (snd (𝔹.bars b' (𝔹In.w1 bi) (⊑-refl· _)))))
  where
    bi : 𝔹In b
    bi = mk𝔹In (fst (𝔹.bars b w1 e1))
                (⊑-trans· e1 (fst (snd (𝔹.bars b w1 e1))))
                (lower (snd (snd (𝔹.bars b w1 e1))))

    b' : 𝔹 O𝔹bars (fst (𝔹.bars b w1 e1))
    b' = fst (i (𝔹In.e1 bi) (𝔹In.br bi))


O𝔹bars∃ : Bars∃ O𝔹bars
O𝔹bars∃ {w} {bar} bars ext =
  fst (bars w (⊑-refl· _)) , fst (snd (bars w (⊑-refl· _))) , lower (snd (snd (bars w (⊑-refl· _))))


O𝔹BarsProps : BarsProps
O𝔹BarsProps =
  mkBarsProps
    O𝔹bars
    O𝔹bars⊑
    O𝔹bars∩
    O𝔹bars∀
--    O𝔹barsFam1
    O𝔹barsFam2
    O𝔹bars∃


{-- We could define open bars as follows, or we can define them directly using inOpenBar as done below
 --}
O𝔹 : 𝕎· → Set(lsuc(L))
O𝔹 w = 𝔹 O𝔹bars w


inOpenBar-Bar-v1 : Bar
inOpenBar-Bar-v1 = BarsProps→Bar O𝔹BarsProps
----



-- f holds in an open bar
inOpenBar : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
inOpenBar w f =
  ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → ∀𝕎 w2 (λ w3 e3 →
     (z : w ⊑· w3) → f w3 z)))


Σ∈𝔹→inOpenBar : (w : 𝕎·) (f : wPred w) → Σ∈𝔹 O𝔹bars f → inOpenBar w f
Σ∈𝔹→inOpenBar w f (b , i) w1 e1 =
  fst (𝔹.bars b w1 e1) ,
  fst (snd (𝔹.bars b w1 e1)) ,
  j
  where
    j : ∀𝕎 (fst (𝔹.bars b w1 e1)) (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    j w2 e2 z = i (⊑-trans· e1 (fst (snd (𝔹.bars b w1 e1)))) (lower (snd (snd (𝔹.bars b w1 e1)))) w2 e2 z



inOpenBar→Σ∈𝔹 : (w : 𝕎·) (f : wPred w) → inOpenBar w f → Σ∈𝔹 O𝔹bars f
inOpenBar→Σ∈𝔹 w f i =
  mk𝔹 bar bars ext mon , j
  where
    bar : 𝕎· → Set L
    bar w0 = Σ 𝕎· λ w1 → Σ (w ⊑· w1) λ e1 → fst (i w1 e1) ⊑· w0

    bars : O𝔹bars w bar
    bars w1 e1 = fst (i w1 e1) , fst (snd (i w1 e1)) , lift (w1 , e1 , ⊑-refl· _)

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (w1 , e1 , e) = ⊑-trans· e1 (⊑-trans· (fst (snd (i w1 e1))) e)

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (w0 , e0 , e') = w0 , e0 , ⊑-trans· e' e

    j : ∈𝔹 {O𝔹bars} (mk𝔹 bar bars ext mon) f
    j {w'} e (w1 , e1 , e') w2 e2 z = snd (snd (i w1 e1)) w2 (⊑-trans· e' e2) z
------



-- f holds in an open bar that depends on another open bar h
inOpenBar' : (w : 𝕎·) {g : wPred w} (h : inOpenBar w g) (f : wPredDep g) → Set(lsuc(L))
inOpenBar' w h f =
  ∀𝕎 w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = fst p in
           let e1 = fst (snd p) in
           let q  = snd (snd p) in
           --∃∀𝕎 w1 (λ w2 e2 → (z : w ⊑· w2) → f w2 z (q w2 e2 z)))
           ∀∃∀𝕎 w1 (λ w2 e2 → (y : w1 ⊑· w2) (z : w ⊑· w2) → f w2 z (q w2 y z)))
           -- The additional ∀ and y are necessary to prove: inOpenBar'→Σ∈𝔹'



------
-- We now show that Σ∈𝔹' {O𝔹bar} andinOpenBar' are equivalent
Σ∈𝔹'→inOpenBar' : (w : 𝕎·) {g : wPred w} (h : Σ∈𝔹 O𝔹bars g) (f : wPredDep g)
                    → Σ∈𝔹' O𝔹bars {w} {g} h f
                    → inOpenBar' w (Σ∈𝔹→inOpenBar w g h) f
Σ∈𝔹'→inOpenBar' w {g} (b , h) f k w1 e1 w1' e1' =
  fst (𝔹.bars b' w3 e3) , fst (snd (𝔹.bars b' w3 e3)) , j
  where
    w2 : 𝕎·
    w2 = fst (𝔹.bars b w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (𝔹.bars b w1 e1))

    b0 : 𝔹.bar b w2
    b0 = lower (snd (snd (𝔹.bars b w1 e1)))

    b' : 𝔹 O𝔹bars w2
    b' = fst (k (⊑-trans· e1 e2) b0)

    w3 : 𝕎·
    w3 = w1'

    e3 : w2 ⊑· w3
    e3 = e1' --⊑-refl· _

    j : ∀𝕎 (proj₁ (𝔹.bars b' w3 e3))
            (λ w4 e4 → (y : w2 ⊑· w4) (z : w ⊑· w4)
                     → f w4 z (snd (snd (Σ∈𝔹→inOpenBar w g (b , h) w1 e1)) w4 y z))
    j w4 e4 y z = snd (k (⊑-trans· e1 e2) b0)
                    (⊑-trans· e3 (fst (snd (𝔹.bars b' w3 e3))))
                    (lower (snd (snd (𝔹.bars b' w3 e3))))
                    w4 e4 y z


inOpenBar'→Σ∈𝔹' : (w : 𝕎·) {g : wPred w} (h : inOpenBar w g) (f : wPredDep g)
                    → inOpenBar' w h f
                    → Σ∈𝔹' O𝔹bars {w} {g} (inOpenBar→Σ∈𝔹 w g h) f
inOpenBar'→Σ∈𝔹' w {g} i f j {w1} e1 (w0 , e0 , ex) =
  B , k
  where
    bar : 𝕎· → Set L
    bar wx = Σ 𝕎· (λ w2 → Σ (w1 ⊑· w2) (λ e2 → fst (j w0 e0 w2 (⊑-trans· ex e2)) ⊑· wx))

    bars : O𝔹bars w1 bar
    bars w2 e2 =
      fst (j w0 e0 w2 (⊑-trans· ex e2)) ,
      fst (snd (j w0 e0 w2 (⊑-trans· ex e2))) ,
      lift (w2 , e2 , ⊑-refl· _)

    ext : {w' : 𝕎·} → bar w' → w1 ⊑· w'
    ext {w'} (w2 , e2 , b) = ⊑-trans· (⊑-trans· e2 (fst (snd (j w0 e0 w2 (⊑-trans· ex e2))))) b

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {wa} {wb} ea (w2 , e2 , eb) = w2 , e2 , ⊑-trans· eb ea

    B : 𝔹 O𝔹bars w1
    B = mk𝔹 bar bars ext mon

    k : ∈𝔹Dep B (snd (inOpenBar→Σ∈𝔹 w g i) e1 (w0 , e0 , ex)) (↑wPredDep'' f e1)
    k {w'} e (wx , ea , eb) w2 e2 x y = c
      where
        c : f w2 y (snd (snd (i w0 e0)) w2 (⊑-trans· ex x) y)
        c = snd (snd (j w0 e0 wx (⊑-trans· ex ea))) w2 (⊑-trans· eb e2) (⊑-trans· ex x) y
-----


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
inOpenBar-inOpenBar' {w} {f} {g} h i w1 e1 w1' e1' = w3 , fst (snd h1) , h3
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h0 = snd (snd (i w1 e1))

    h1 : ∃∀𝕎 w1' (λ w' e' → (z : w ⊑· w') (x : f w' z) → g w' z x)
    h1 = h w1' (⊑-trans· (⊑-trans· e1 e2) e1')

    w3 : 𝕎·
    w3 = fst h1

    e3 : w1' ⊑· w3
    e3 = fst (snd h1)

    h2 : ∀𝕎 w3 (λ w' e' → (z : w ⊑· w') (x : f w' z) → g w' z x)
    h2 = snd (snd h1)

    h3 : ∀𝕎 w3 (λ w4 e4 → (y : w2 ⊑· w4) (z : w ⊑· w4) → g w4 z (h0 w4 y z)) -- (⊑-trans· e1' (⊑-trans· e3 e4))
    h3 w4 e4 y z = h2 w4 e4 z (h0 w4 y z) -- (⊑-trans· e1' (⊑-trans· e3 e4))



{--
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
--}



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



↑inOpenBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f) {w' : 𝕎·} (e : w ⊑· w')
              → inOpenBar' w i g → inOpenBar' w' (↑inOpenBar i e) (↑wPredDep g e)
↑inOpenBar' {w} {f} {g} i {w'} e j w1 e1 w1' e1' =
  w2 , e2 , h
  where
    w2 : 𝕎·
    w2 = fst (j w1 (⊑-trans· e e1) w1' e1')

    e2 : w1' ⊑· w2
    e2 = fst (snd (j w1 (⊑-trans· e e1) w1' e1'))

    h : ∀𝕎 w2 (λ w3 e3 → (y : fst (↑inOpenBar i e w1 e1) ⊑· w3) (z : w' ⊑· w3)
                       → ↑wPredDep g e w3 z (snd (snd (↑inOpenBar i e w1 e1)) w3 y z)) -- (⊑-trans· e1' (⊑-trans· e2 e3))
    h w3 e3 y z = snd (snd (j w1 (⊑-trans· e e1) w1' e1')) w3 e3 y (⊑-trans· e z)
--snd (snd (j w1 (⊑-trans· e e1) w1' e1')) w3 e3 ? ? -- (⊑-trans· e z)



inOpenBar-const : {w : 𝕎·} {t : Set(lsuc(L))} → inOpenBar w (λ w e → t) → t
inOpenBar-const {w} {t} h = snd (snd (h w (⊑-refl· w))) (fst (h w (⊑-refl· w))) (⊑-refl· _) (fst (snd (h w (⊑-refl· w))))




{--
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
--}



inOpenBar'-idem : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                  → inOpenBar w (λ w' e' → inOpenBar' w' (↑'inOpenBar i e') (↑wPredDep' g e'))
                  → inOpenBar' w i g
inOpenBar'-idem {w} {f} {g} i h w1 e1 w0 e0 =
  w4 , e4 ,  h5
  where
    w1' : 𝕎·
    w1' = w0 --fst (i w1 e1)

    e1' : w1 ⊑· w1'
    e1' = ⊑-trans· (fst (snd (i w1 e1))) e0 --fst (snd (i w1 e1))

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

    h4 : ∃∀𝕎 w3 (λ w' e' → (y : w3 ⊑· w') (z : w2 ⊑· w')
                            → ↑wPredDep'
                                g
                                (⊑-trans· (⊑-trans· e1 e1') e2)
                                w' z
                                (snd (snd (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))) w' e' z))
    h4 = h3 w2 (⊑-refl· w2) w3 (⊑-refl· w3) --h3 w2 (⊑-refl· w2) w3 ? (⊑-refl· w3)

    w4 : 𝕎·
    w4 = fst h4

    e4 : w1' ⊑· w4
    e4 = ⊑-trans· (⊑-trans· e2 e3) (fst (snd h4))

    h5 : ∀𝕎 w4 (λ w' e' → (y : fst (i w1 e1) ⊑· w') (z : w ⊑· w') → g w' z (snd (snd (i w1 e1)) w' y z))
--(⊑-trans· e0 (⊑-trans· e4 e'))
    h5 w5 e5 y z = a2
      where
        a1 : ↑wPredDep' g
                        (⊑-trans· (⊑-trans· e1 e1') e2)
                        w5 (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5)
                        (snd (snd (↑'inOpenBar i (⊑-trans· (⊑-trans· e1 e1') e2) w2 (⊑-refl· w2))) w5 (⊑-trans· (fst (snd h4)) e5) (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5))
        a1 = snd (snd h4) w5 e5 (⊑-trans· (fst (snd h4)) e5) (⊑-trans· (⊑-trans· e3 (fst (snd h4))) e5)

        a2 : g w5 z (snd (snd (i w1 e1)) w5 y z) -- (⊑-trans· e0 (⊑-trans· e4 e5))
        a2 = a1 z (snd (snd (i w1 e1)) w5 y z) --(⊑-trans· e0 (⊑-trans· e4 e5))



{--
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
--}





∀𝕎-inOpenBar-inOpenBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inOpenBar w f)
                            → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : atOpenBar i w' e' x)--} → g w' e' x)
                            → inOpenBar' w i g
∀𝕎-inOpenBar-inOpenBar' {w} {f} {g} i h w1 e1 w0 e0 =
  w2 ,
  ⊑-refl· w2 ,
  λ w3 e3 y z → h w3 z (snd (snd (i w1 e1)) w3 y z)
--h w3 z (h0 w3 (⊑-trans· (⊑-refl· w2) e3) z) {--(ATOPENBAR-O w1 e1 w3 (⊑-trans· (⊑-refl· (fst (i w1 e1))) e3) z)--}
  where
    w2 : 𝕎·
    w2 = w0 --fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = ⊑-trans· (fst (snd (i w1 e1))) e0

--    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
--    h0 = ∀𝕎-mon e0 (snd (snd (i w1 e1)))



inOpenBar'-comb : {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : inOpenBar w f)
              → ∀𝕎 w (λ w' e' → (z : f w' e') (zg : f w' e') (zh : f w' e')
                                 → g w' e' zg → h w' e' zh → k w' e' z)
              → inOpenBar' w i g → inOpenBar' w i h → inOpenBar' w i k
inOpenBar'-comb {w} {f} {g} {h} {k} i aw ig ih w1 e1 w0 e0 =
  w5 ,
  ⊑-trans· (⊑-trans· e3 e4) e5 ,
  λ w6 e6 y z → aw w6 z
                 (snd (snd (i w1 e1)) w6 y z)
                 (h4 w6 (⊑-trans· (⊑-refl· _) (⊑-trans· e5 e6)) z)
                 (h2 w6 (⊑-trans· e3 (⊑-trans· (⊑-trans· e4 e5) e6)) z)
                 (h5 w6 e6 (⊑-trans· (⊑-refl· _) (⊑-trans· e5 e6)) z)
                 (h3 w6 (⊑-trans· (⊑-trans· e4 e5) e6) (⊑-trans· e0 (⊑-trans· e3 (⊑-trans· (⊑-trans· e4 e5) e6))) z)
  where
    w2 : 𝕎·
    w2 = w0 --fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = ⊑-trans· (fst (snd (i w1 e1))) e0

    h2 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h2 = ∀𝕎-mon e0 (snd (snd (i w1 e1)))

    w3 : 𝕎·
    w3 = fst (ih w1 e1 w0 e0)

    e3 : w2 ⊑· w3
    e3 = fst (snd (ih w1 e1 w0 e0))

    h3 : ∀𝕎 w3 (λ w4 e4 → (y : fst (i w1 e1) ⊑· w4) (z : w ⊑· w4) → h w4 z (snd (snd (i w1 e1)) w4 y z))
    h3 = snd (snd (ih w1 e1 w0 e0))

    w4 : 𝕎·
    w4 = fst (i w3 (⊑-trans· (⊑-trans· e1 e2) e3))

    e4 : w3 ⊑· w4
    e4 = fst (snd (i w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    h4 : ∀𝕎 w4 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h4 = snd (snd (i w3 (⊑-trans· (⊑-trans· e1 e2) e3)))

    w5 : 𝕎·
    w5 = fst (ig w3 (⊑-trans· (⊑-trans· e1 e2) e3) w4 (⊑-refl· _))

    e5 : w4 ⊑· w5
    e5 = fst (snd (ig w3 (⊑-trans· (⊑-trans· e1 e2) e3) w4 (⊑-refl· _)))

    h5 : ∀𝕎 w5 (λ w6 e6 → (y : w4 ⊑· w6) (z : w ⊑· w6) → g w6 z (h4 w6 y z))
    h5 = snd (snd (ig w3 (⊑-trans· (⊑-trans· e1 e2) e3) w4 (⊑-refl· _)))



{--
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
--}



∀𝕎-inOpenBar'-inOpenBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inOpenBar w f)
                            → ∀𝕎 w (λ w' e' → (x : f w' e') {--→ atOpenBar i w' e' x--} → g w' e' x → h w' e')
                            → inOpenBar' w i g → inOpenBar w h
∀𝕎-inOpenBar'-inOpenBar {w} {f} {g} {h} i a q w1 e1 =
  w3 ,
  ⊑-trans· e2 e3 ,
  λ w4 e4 z → a w4 z (h0 w4 (⊑-trans· (⊑-refl· _) (⊑-trans· e3 e4)) z) (h3 w4 e4 (⊑-trans· (⊑-refl· _) (⊑-trans· e3 e4)) z)
  where
    w2 : 𝕎·
    w2 = fst (i w1 e1)

    e2 : w1 ⊑· w2
    e2 = fst (snd (i w1 e1))

    h0 : ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    h0 = snd (snd (i w1 e1))

    w3 : 𝕎·
    w3 = fst (q w1 e1 w2 (⊑-refl· _))

    e3 : w2 ⊑· w3
    e3 = fst (snd (q w1 e1 w2 (⊑-refl· _)))

    h3 : ∀𝕎 w3 (λ w4 e4 → (y : w2 ⊑· w4) (z : w ⊑· w4) → g w4 z (h0 w4 y z))
    h3 = snd (snd (q w1 e1 w2 (⊑-refl· _)))



{--
old-inOpenBar'-change : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i j : inOpenBar w f)
                    → ∀𝕎 w (λ w' e' → (x y : f w' e') {--→ atOpenBar i w' e' x → atOpenBar j w' e' y--} → g w' e' x → g w' e' y)
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
         {--(ATOPENBAR-O w2 (⊑-trans· e1 e2) w5  (⊑-trans· e4 e5) z)
         (ATOPENBAR-O w1 e1 w5  (⊑-trans· (⊑-trans· e3 e4) e5) z)--}
         (h0 w5 e5 z)
--}



inOpenBar'-change : {w : 𝕎·} {f : wPred w} {k : wPred w} {g : wPredDep f} {h : wPredDep k}
                    (i : inOpenBar w f) (j : inOpenBar w k)
                    → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e') {--→ atOpenBar i w' e' x → atOpenBar j w' e' y--}
                                      → g w' e' x → h w' e' y)
                    → inOpenBar' w i g → inOpenBar' w j h
inOpenBar'-change {w} {f} {k} {g} {h} i j aw b w1 e1 w0 e0 =
  w4 , ⊑-trans· e3 e4 , h1
  where
    w2 : 𝕎·
    w2 = w0 --fst (j w1 e1)

    e2 : w1 ⊑· w2
    e2 = ⊑-trans· (fst (snd (j w1 e1))) e0

    w3 : 𝕎·
    w3 = fst (i w2 (⊑-trans· e1 e2))

    e3 : w2 ⊑· w3
    e3 = fst (snd (i w2 (⊑-trans· e1 e2)))

    w4 : 𝕎·
    w4 = fst (b w2 (⊑-trans· e1 e2) w3 (⊑-refl· _))

    e4 : w3 ⊑· w4
    e4 = fst (snd (b w2 (⊑-trans· e1 e2) w3 (⊑-refl· _)))

    h0 : ∀𝕎 w4 (λ w5 e5 → (y : w3 ⊑· w5) (z : w ⊑· w5) → g w5 z (snd (snd (i w2 (⊑-trans· e1 e2))) w5 y z))
    h0 = snd (snd (b w2 (⊑-trans· e1 e2) w3 (⊑-refl· _)))

    h1 : ∀𝕎 w4 (λ w5 e5 → (y : fst (j w1 e1) ⊑· w5) (z : w ⊑· w5) → h w5 z (snd (snd (j w1 e1)) w5 y z))
    h1 w5 e5 y z =
      aw w5 z
         (snd (snd (i w2 (⊑-trans· e1 e2))) w5 (⊑-trans· (⊑-refl· _) (⊑-trans· e4 e5)) z)
         (snd (snd (j w1 e1)) w5 y z)
         (h0 w5 e5 (⊑-trans· (⊑-refl· _) (⊑-trans· e4 e5)) z)


inOpenBar'-comb-change : {w : 𝕎·} {f₁ f₂ f₃ : wPred w}
                         {g₁ : wPredDep f₁} {g₂ : wPredDep f₂} {g₃ : wPredDep f₃}
                         (i₁ : inOpenBar w f₁) (i₂ : inOpenBar w f₂) (i₃ : inOpenBar w f₃)
                         → ∀𝕎 w (λ w' e' → (x₁ : f₁ w' e') (x₂ : f₂ w' e') (x₃ : f₃ w' e')
                                          → g₁ w' e' x₁ → g₂ w' e' x₂ → g₃ w' e' x₃)
                         → inOpenBar' w i₁ g₁ → inOpenBar' w i₂ g₂ → inOpenBar' w i₃ g₃
inOpenBar'-comb-change {w} {f₁} {f₂} {f₃} {g₁} {g₂} {g₃} i₁ i₂ i₃ aw b₁ b₂ w1 e1 w0 e0 =
  w6 , ⊑-trans· e3 (⊑-trans· e4 (⊑-trans· e5 e6)) , h2
  where
    w2 : 𝕎·
    w2 = w0

    e2 : w1 ⊑· w2
    e2 = ⊑-trans· (fst (snd (i₃ w1 e1))) e0

    -- 1st bar
    w3 : 𝕎·
    w3 = fst (i₁ w2 (⊑-trans· e1 e2))

    e3 : w2 ⊑· w3
    e3 = fst (snd (i₁ w2 (⊑-trans· e1 e2)))

    w4 : 𝕎·
    w4 = fst (b₁ w2 (⊑-trans· e1 e2) w3 (⊑-refl· _))

    e4 : w3 ⊑· w4
    e4 = fst (snd (b₁ w2 (⊑-trans· e1 e2) w3 (⊑-refl· _)))

    h0 : ∀𝕎 w4 (λ w5 e5 → (y : w3 ⊑· w5) (z : w ⊑· w5) → g₁ w5 z (snd (snd (i₁ w2 (⊑-trans· e1 e2))) w5 y z))
    h0 = snd (snd (b₁ w2 (⊑-trans· e1 e2) w3 (⊑-refl· _)))

    -- 2nd bar
    w5 : 𝕎·
    w5 = fst (i₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))))

    e5 : w4 ⊑· w5
    e5 = fst (snd (i₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4)))))

    w6 : 𝕎·
    w6 = fst (b₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) w5 (⊑-refl· _))

    e6 : w5 ⊑· w6
    e6 = fst (snd (b₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) w5 (⊑-refl· _)))

    h1 : ∀𝕎 w6 (λ w7 e7 → (y : w5 ⊑· w7) (z : w ⊑· w7) → g₂ w7 z (snd (snd (i₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))))) w7 y z))
    h1 = snd (snd (b₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) w5 (⊑-refl· _)))

    h2 : ∀𝕎 w6 (λ w7 e7 → (y : fst (i₃ w1 e1) ⊑· w7) (z : w ⊑· w7) → g₃ w7 z (snd (snd (i₃ w1 e1)) w7 y z))
    h2 w7 e7 y z =
      aw w7 z
         (snd (snd (i₁ w2 (⊑-trans· e1 e2))) w7 (⊑-trans· (⊑-refl· _) (⊑-trans· e4 (⊑-trans· e5 (⊑-trans· e6 e7)))) z)
         (snd (snd (i₂ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))))) w7 (⊑-trans· (⊑-refl· _) (⊑-trans· e6 e7)) z)
         (snd (snd (i₃ w1 e1)) w7 y z)
         (h0 w7 (⊑-trans· e5 (⊑-trans· e6 e7)) (⊑-trans· (⊑-refl· _) (⊑-trans· e4 (⊑-trans· e5 (⊑-trans· e6 e7)))) z)
         (h1 w7 e7 (⊑-trans· (⊑-refl· _) (⊑-trans· e6 e7)) z)



-- We can prove that open-bars satisfy the Bar properties
inOpenBar-Bar : Bar
inOpenBar-Bar =
  mkBar
    inOpenBar
    inOpenBar'
    ↑inOpenBar
    ↑'inOpenBar
    (λ {w} {f} {g} → ↑inOpenBar' {w} {f} {g}) -- why??
    inOpenBarFunc
    ∀𝕎-inOpenBarFunc
    inOpenBar-inOpenBar'
    ∀𝕎-inOpenBar-inOpenBar'
    ∀𝕎-inOpenBar
    inOpenBar-idem
    (λ {w} {f} {g} → inOpenBar'-idem {w} {f} {g})
    ∀𝕎-inOpenBar'-inOpenBar
--    inOpenBar'-comb
--    inOpenBar'-change
    inOpenBar'-comb-change
    inOpenBar-const


    --atOpenBar
    --(λ i → ATOPENBAR-R)
--    wPredDepExtIrr-inOpenBar
--    (λ {w} {f} {g} → ↑inOpenBar' {w} {f} {g})
--    atOpenBar
    --(λ {w} {f} {g} {h} → inOpenBar'-inOpenBar' {w} {f} {g} {h})
--    inOpenBar-mon
--    inOpenBar-idem2
--    (λ {w} {f} {g} → inOpenBar'-idem2 {w} {f} {g})
    {--∀𝕎-inOpenBar'-inOpenBar--}
--    old-inOpenBar'-change

\end{code}
