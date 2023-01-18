\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; pred)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Empty


open import world

module counterexamples where

𝕄 : Set₀
𝕄 = ℕ ⊎ ℕ

_⊂_ : 𝕄 → 𝕄 → Set₀
_⊂_ (inj₁ n) (inj₁ m) = n ≤ m
_⊂_ (inj₂ n) (inj₂ m) = n ≤ m
_⊂_ (inj₁ _) (inj₂ _) = ⊥
_⊂_ (inj₂ _) (inj₁ _) = ⊥

⊂-refl : (a : 𝕄) → a ⊂ a
⊂-refl (inj₁ n) = ≤-refl
⊂-refl (inj₂ n) = ≤-refl

⊂-trans : {a b c : 𝕄} → a ⊂ b → b ⊂ c → a ⊂ c
⊂-trans {inj₁ _} {inj₁ _} {inj₁ _} a⊂b b⊂c = ≤-trans a⊂b b⊂c
⊂-trans {inj₂ _} {inj₂ _} {inj₂ _} a⊂b b⊂c = ≤-trans a⊂b b⊂c

W : PossibleWorlds
W = mkPossibleWorlds 𝕄 _⊂_ ⊂-refl ⊂-trans

open import worldDef(W)
open import bar{0ℓ}{0ℓ}(W)
open import nucleus(W)

-- AIM: falsify the meet-preservation property of the nucleus associated with a barring predicate

is-left : Subset → Set₀
is-left U = (w : 𝕎·) → w ∈ U → Σ[ n ∈ ℕ ] w ≡ inj₁ n

is-right : Subset → Set₀
is-right U = (w : 𝕎·) → w ∈ U → Σ[ n ∈ ℕ ] w ≡ inj₂ n

-- This is our Terrible Kripke (Tripke) barring which somehow satisfies all CoversProps
T𝔹bars : Bars
T𝔹bars w U = w ∈ U × (is-left U ⊎ is-right U)

T𝔹bars⊑ : Bars⊑ T𝔹bars
T𝔹bars⊑ {w1} {w2} w1⊑w2 U (w1∈U , inj₁ U-left)  = (w1 , w1∈U , w1⊑w2 , ⊑-refl· w2) , inj₁ resU-left
  where
    resU-left : is-left (bar⊑ w2 U)
    resU-left (inj₁ n) (inj₁ _ , _) = n , refl
    resU-left (inj₂ _) (inj₂ m , m∈U , _) with U-left (inj₂ m) m∈U
    ... | ()
T𝔹bars⊑ {w1} {w2} w1⊑w2 U (w1∈U , inj₂ U-right) = (w1 , w1∈U , w1⊑w2 , ⊑-refl· w2) , inj₂ resU-right
  where
    resU-right : is-right (bar⊑ w2 U)
    resU-right (inj₂ n) (inj₂ _ , _) = n , refl
    resU-right (inj₁ _) (inj₁ m , m∈U , _) with U-right (inj₁ m) m∈U
    ... | ()


T𝔹bars∩ : Bars∩ T𝔹bars
T𝔹bars∩ {inj₁ x} U V (w∈U , inj₁ U-left)  (w∈V , _) = (inj₁ x , inj₁ x , w∈U , w∈V , ⊑-refl· (inj₁ x) , ⊑-refl· (inj₁ x)) , inj₁ bar∩-left
  where
    bar∩-left : is-left (bar∩ U V)
    bar∩-left (inj₁ n) _ = n , refl
    bar∩-left (inj₂ _) (inj₂ m , _ , w2∈U , _) with U-left (inj₂ m) w2∈U
    ... | ()
T𝔹bars∩ {inj₂ x} U V (w∈U , inj₂ U-right) (w∈V , _) = (inj₂ x , inj₂ x , w∈U , w∈V , ⊑-refl· (inj₂ x) , ⊑-refl· (inj₂ x)) , inj₂ bar∩-right
  where
    bar∩-right : is-right (bar∩ U V)
    bar∩-right (inj₂ n) _ = n , refl
    bar∩-right (inj₁ _) (inj₁ m , _ , w2∈U , _) with U-right (inj₁ m) w2∈U
    ... | ()
T𝔹bars∩ {inj₂ x} U V (w∈U , inj₁ U-left)  (w∈V , _) with U-left (inj₂ x) w∈U
... | ()
T𝔹bars∩ {inj₁ x} U V (w∈U , inj₂ U-right) (w∈V , _) with U-right (inj₁ x) w∈U
... | ()

T𝔹bars∀ : Bars∀ T𝔹bars
T𝔹bars∀ (inj₁ n) = ⊑-refl· (inj₁ n) , inj₁ bar∀-left
  where
    bar∀-left : is-left (bar∀ (inj₁ n))
    bar∀-left (inj₁ m) _ = m , refl
T𝔹bars∀ (inj₂ n) = ⊑-refl· (inj₂ n) , inj₂ bar∀-right
  where
    bar∀-right : is-right (bar∀ (inj₂ n))
    bar∀-right (inj₂ m) _ = m , refl

inj₁-covered⇒is-left : (n : ℕ) (U : Subset) → T𝔹bars (inj₁ n) U → is-left U
inj₁-covered⇒is-left n U (_   , inj₁ U-left)  = U-left
inj₁-covered⇒is-left n U (n∈U , inj₂ U-right) with U-right (inj₁ n) n∈U
... | ()

inj₂-covered⇒is-right : (n : ℕ) (U : Subset) → T𝔹bars (inj₂ n) U → is-right U
inj₂-covered⇒is-right n U (_   , inj₂ U-right)  = U-right
inj₂-covered⇒is-right n U (n∈U , inj₁ U-left) with U-left (inj₂ n) n∈U
... | ()

T𝔹barsFam2 : BarsFam2 T𝔹bars
T𝔹barsFam2 {_} {inj₁ n} (mk𝔹 U (w∈U , inj₁ U-left) U-ext U-mon) G i = (index , w∈iw) , inj₁ barFam2-left
  where
    𝔹w = mk𝔹 U (w∈U , inj₁ U-left) U-ext U-mon

    index : 𝔹In 𝔹w
    index = mk𝔹In (inj₁ n) (⊑-refl· (inj₁ n)) w∈U

    w∈iw : inj₁ n ∈ 𝔹.bar (fst (i (⊑-refl· (inj₁ n)) w∈U))
    w∈iw = fst (𝔹.bars (fst (i (⊑-refl· (inj₁ n)) w∈U)))

    Uind-left : (ind : 𝔹In 𝔹w) → is-left (𝔹.bar (fst (i (𝔹In.e1 ind) (𝔹In.br ind))))
    Uind-left (mk𝔹In (inj₁ m) n≤m m∈Uind) = inj₁-covered⇒is-left m _ (𝔹.bars (fst (i n≤m m∈Uind )))

    barFam2-left : is-left (barFam2 𝔹w G i)
    barFam2-left (inj₁ m) _ = m , refl
    barFam2-left (inj₂ m) (ind , m∈Uind) with (Uind-left ind) (inj₂ m) m∈Uind
    ... | ()
T𝔹barsFam2 {_} {inj₂ n} (mk𝔹 U (w∈U , inj₂ U-right) U-ext U-mon) G i = ((index , w∈iw)) , inj₂ barFam2-right
  where
    𝔹w = mk𝔹 U (w∈U , inj₂ U-right) U-ext U-mon

    index : 𝔹In 𝔹w
    index = mk𝔹In (inj₂ n) (⊑-refl· (inj₂ n)) w∈U

    w∈iw : inj₂ n ∈ 𝔹.bar (fst (i (⊑-refl· (inj₂ n)) w∈U))
    w∈iw = fst (𝔹.bars (fst (i (⊑-refl· (inj₂ n)) w∈U)))

    Uind-right : (ind : 𝔹In 𝔹w) → is-right (𝔹.bar (fst (i (𝔹In.e1 ind) (𝔹In.br ind))))
    Uind-right (mk𝔹In (inj₂ m) n≤m m∈Uind) = inj₂-covered⇒is-right m _ (𝔹.bars (fst (i n≤m m∈Uind )))

    barFam2-right : is-right (barFam2 𝔹w G i)
    barFam2-right (inj₂ m) _ = m , refl
    barFam2-right (inj₁ m) (ind , m∈Uind) with (Uind-right ind) (inj₁ m) m∈Uind
    ... | ()
T𝔹barsFam2 {_} {inj₁ n} (mk𝔹 _ (w∈U , inj₂ U-right) _ _) _ _ with U-right (inj₁ n) w∈U
... | ()
T𝔹barsFam2 {_} {inj₂ n} (mk𝔹 _ (w∈U , inj₁ U-left) _ _)  _ _ with U-left  (inj₂ n) w∈U
... | ()

T𝔹bars∃ : Bars∃ T𝔹bars
T𝔹bars∃ {w} {U} (w∈U , _) _ = w , ⊑-refl· w , w∈U

-- And for the final blow, we see that this relation is not extensive:

T𝔹bars-is-bad : Σ[ w ∈ 𝕎· ] Σ[ U ∈ Subset ] w ∈ U × ¬ T𝔹bars w U
T𝔹bars-is-bad = inj₁ 0 , (λ _ → ⊤) , tt , ¬w◀U
  where
   ¬w◀U : ¬ T𝔹bars (inj₁ 0) (λ _ → ⊤)
   ¬w◀U w◀U with inj₂-covered⇒is-right 0 (λ _ → ⊤) (tt , snd w◀U) (inj₁ 0) tt
   ... | ()

-- As a result of the discussion in coversPropsImplyCucleus.lagda, the mapping UCSubset → UCSubset
-- induced by T𝔹bars will also not be monotonic and as a result will not preserve meets.

\end{code}
