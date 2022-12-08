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


module space {L : Level} (W : PossibleWorlds {L}) --(E : Extensionality L (lsuc(L)))
       where
open import worldDef{L}(W)
open import bar(W)




simb : Br → Br → Set(L)
simb b1 b2 = (w : 𝕎·) → (b1 w → b2 w) × (b2 w → b1 w)


BarsE : Bars → Set(lsuc L)
BarsE bars =
  (w : 𝕎·) {b b' : Br} → bars w b → simb b' b → bars w b'


BarsWf : Bars → Set(lsuc L)
BarsWf bars =
  (w w' : 𝕎·) {b : Br} → bars w b → b w' → w ⊑· w'


Bars⊑×Bars∩→Bars∩' : {bars : Bars} → Bars⊑ bars → Bars∩ bars → Bars∩' bars
Bars⊑×Bars∩→Bars∩' {bars} bars⊑ bars∩ {w1} {w2} e b1 b2 bars1 bars2 =
  {!!} --subst (bars w2) {!!} {--(E ptwise)--} bars∩⊑
  where
  bars∩⊑ : bars w2 (bar∩ (bar⊑ w2 b1) b2)
  bars∩⊑ = bars∩ (bar⊑ w2 b1) b2 (bars⊑ e b1 bars1) bars2

  ptwise : (w0 : 𝕎·) → bar∩ (bar⊑ w2 b1) b2 w0 ≡ bar∩' w2 b1 b2 w0
  ptwise w0 = {!!}

--thing'' : (w0 : 𝕎·) → bar∩ (bar⊑ w2 b1) b2 w0 → bar∩' w2 b1 b2 w0
--thing'' w0 (w3 , w4 , (w5 , b15 , e53 , e23) , b24 , e30 , e40) = w5 , w4 , b15 , b24 , ⊑-trans· e53 e30 , e40 , ⊑-trans· e23 e30
--
--thing''' : (w0 : 𝕎·) → bar∩' w2 b1 b2 w0 → bar∩ (bar⊑ w2 b1) b2 w0
--thing''' w0 (w3 , w4 , b13 , b24 , e30 , e40 , e20) = (w0 , w4 , (w3 , b13 , e30 , e20) , b24 , ⊑-refl· w0 , e40)

Bars∩'→Bars∩ : {bars : Bars} → Bars∩' bars → Bars∩ bars
Bars∩'→Bars∩ {bars} bars∩' {w1} b1 b2 b11 b21 = {!!} --subst (bars w1) (E ptwise) bars∩
  where
  bars∩ : bars w1 (bar∩' w1 b1 b2)
  bars∩ = bars∩' (⊑-refl· w1) b1 b2 b11 b21

  ptwise : (w0 : 𝕎·) → bar∩' w1 b1 b2 w0 ≡ bar∩ b1 b2 w0
  ptwise w0 = {!!}

-- bar∩' w1 b1 b2 w0 = Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → b1 w1 × b2 w2 × w1 ⊑· w0 × w2 ⊑· w0 × w1 ⊑· w0))
-- bar∩ b1 b2 w0     = Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → b1 w1 × b2 w2 × w1 ⊑· w0 × w2 ⊑· w0))
-- If we assume that w1 ⊑· w0 is a proposition, then these should be the same on the nose
-- they also imply each other:
-- to go from top to bottom we forget one of the proofs for w1 ⊑· w0
-- to go from bottom to top we duplicate the proof of w1 ⊑· w0

Bars∩'×Bars∀→Bars⊑ : {bars : Bars} → Bars∩' bars → Bars∀ bars → Bars⊑ bars
Bars∩'×Bars∀→Bars⊑ {bars} bars∩' bars∀ {w1} {w2} e12 b1 b11 = {!!} --subst (bars w2) (E ptwise) bars⊑
  where
  bars⊑ : bars w2 (bar∩' w2 b1 (bar∀ w2))
  bars⊑ = bars∩' e12 b1 (bar∀ w2) b11 (bars∀ w2)

  ptwise : (w0 : 𝕎·) → bar∩' w2 b1 (bar∀ w2) w0 ≡ bar⊑ w2 b1 w0
  ptwise w0 = {!!}

-- bar∩' w2 b1 (bar∀ w2) w0 = Σ 𝕎· (λ w3 → Σ 𝕎· (λ w4 → b1 w3 × w2 ⊑· w4 × w3 ⊑· w0 × w4 ⊑· w0 × w2 ⊑· w0))
-- bar⊑ w2 b1 w0            = Σ 𝕎· (λ w3 →              b1 w3 ×            w3 ⊑· w0            × w2 ⊑· w0)
-- Going from top to bottom is easy, we just forget the relevant entries
-- To go from bottom to top, we can use w2 for w4
-- I don't think these are the same though on the nose, they simply imply each other?



Bars∩'' : (B : Bars) → Set(lsuc(L))
Bars∩'' B =
  {w1 w2 : 𝕎·} (e : w1 ⊑· w2) (b1 b2 : Br)
  → B w1 b1
  → B w2 b2
  → B w2 (bar∩ b1 b2)


𝔹∩'' : {B : Bars} (isect : Bars∩'' B) {w1 w2 : 𝕎·} (e : w1 ⊑· w2) → 𝔹 B w1 → 𝔹 B w2 → 𝔹 B w2
𝔹∩'' {B} isect {w1} {w2} e (mk𝔹 b1 bars1 ext1 mon1) (mk𝔹 b2 bars2 ext2 mon2) =
  mk𝔹 bar bars ext mon
  where
    bar : Br
    bar = bar∩ b1 b2

    bars : B w2 bar
    bars = isect e b1 b2 bars1 bars2

    ext : {w0 : 𝕎·} → bar w0 → w2 ⊑· w0
    ext {w0} (w3 , w4 , b13 , b24 , e30 , e40) = ⊑-trans· (ext2 b24) e40 --e20

    mon : {w3 w4 : 𝕎·} → w3 ⊑· w4 → bar w3 → bar w4
    mon {w3} {w4} e34 (w5 , w6 , b15 , b26 , e53 , e63) = w5 , w6 , b15 , b26 , ⊑-trans· e53 e34 , ⊑-trans· e63 e34


Bars⊑×Bars∩→Bars∩'' : {bars : Bars} → BarsE bars → BarsWf bars → Bars⊑ bars → Bars∩ bars → Bars∩'' bars
Bars⊑×Bars∩→Bars∩'' {bars} ext wf bars⊑ bars∩ {w1} {w2} e b1 b2 bars1 bars2 =
  ext w2 bars∩⊑ sim
  where
    bars∩⊑ : bars w2 (bar∩ (bar⊑ w2 b1) b2)
    bars∩⊑ = bars∩ (bar⊑ w2 b1) b2 (bars⊑ e b1 bars1) bars2

    sim : simb (bar∩ b1 b2) (bar∩ (bar⊑ w2 b1) b2)
    sim w = i1 , i2
      where
        i1 : bar∩ b1 b2 w → bar∩ (bar⊑ w2 b1) b2 w
        i1 (z1 , z2 , x1 , x2 , y1 , y2) = w , z2 , (z1 , x1 , y1 , ⊑-trans· (wf w2 z2 bars2 x2) y2) , x2 , ⊑-refl· w , y2 --z2 , z2 , (z2 , {!!} , {!!} , {!!}) , x2 , y2 , y2

        i2 : bar∩ (bar⊑ w2 b1) b2 w → bar∩ b1 b2 w
        i2 (z1 , z2 , (x1 , a1 , a2 , a3) , x2 , y1 , y2) = x1 , z2 , a1 , x2 , ⊑-trans· a2 y1 , y2


Bars∩''→Bars∩ : {bars : Bars} → Bars∩'' bars → Bars∩ bars
Bars∩''→Bars∩ {bars} bars∩'' {w1} b1 b2 b11 b21 = bars∩'' {w1} {w1} (⊑-refl· w1) b1 b2 b11 b21


Bars∩''×Bars∀→Bars⊑ : {bars : Bars} → Bars∩'' bars → Bars∀ bars → Bars⊑ bars
Bars∩''×Bars∀→Bars⊑ {bars} bars∩' bars∀ {w1} {w2} e12 b1 b11 = {!!}

\end{code}
