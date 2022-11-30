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


module space {L : Level} (W : PossibleWorlds {L}) (E : Extensionality L (lsuc(L)))
       where
open import worldDef{L}(W)
open import bar(W)




simb : Br → Br → Set(L)
simb b1 b2 = (w : 𝕎·) → (b1 w → b2 w) × (b2 w → b1 w)


BarsE : Bars → Set(lsuc L)
BarsE bars =
  (w : 𝕎·) (b b' : Br) → bars w b → simb b' b → bars w b'


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
Bars∩'→Bars∩ {bars} bars∩' {w1} b1 b2 b11 b21 = subst (bars w1) (E ptwise) bars∩
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
Bars∩'×Bars∀→Bars⊑ {bars} bars∩' bars∀ {w1} {w2} e12 b1 b11 = subst (bars w2) (E ptwise) bars⊑
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



\end{code}
