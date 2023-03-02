\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; _⊔_ ; Setω) renaming (suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Sum
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; pred)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open import Relation.Nullary
open import Data.Empty


open import util
open import calculus
open import world


module bar {n : Level} (m : Level) (W : PossibleWorlds {n})
       where
open import worldDef(W)
open import nucleus(W)


{-----------------------------------------
 --
 -- Generic bar type
 --
 --}

Coverage : Set (lsuc n ⊔ lsuc m)
Coverage = 𝕎· → UCSubset → Set m

record 𝔹 (_◀_ : Coverage) (w : 𝕎·) : Set (lsuc n ⊔ lsuc m) where
  constructor mk𝔹
  field
    U      : UCSubset
    covers : w ◀ U
    ext    : {w' : 𝕎·} → w' ∈· U → w ⊑· w'

{-- Bars and dependent bars --}
∈𝔹 : ∀ {l} {_◀_ : Coverage} {w : 𝕎·} (b : 𝔹 _◀_ w) (f : wPred {l} w) → Set (n ⊔ l)
∈𝔹 {_} {_} {w} b f = {w' : 𝕎·} (e : w ⊑· w') → w' ∈· (𝔹.U b) → ∀𝕎 w' (↑wPred' f e)
{-# INLINE ∈𝔹 #-}

Σ∈𝔹 : ∀ {l} (_◀_ : Coverage) {w : 𝕎·} (f : wPred {l} w) → Set (lsuc n ⊔ lsuc m ⊔ l)
Σ∈𝔹 _◀_ {w} f = Σ (𝔹 _◀_ w) (λ b → ∈𝔹 b f)
{-# INLINE Σ∈𝔹 #-}

∈𝔹Dep : ∀ {l} {_◀_ : Coverage} {w : 𝕎·} (b : 𝔹 _◀_ w) {g : wPred {l} w} (i : ∀𝕎 w g) (f : wPredDep g) → Set (n ⊔ l)
∈𝔹Dep {_} {_} {w} b {g} i f =
  {w' : 𝕎·} (e : w ⊑· w') → w' ∈· (𝔹.U b) → ∀𝕎 w' (λ w'' e' → (x : w ⊑· w'') → f w'' x (i w'' x))
{-# INLINE ∈𝔹Dep #-}

Σ∈𝔹' : ∀ {l} (_◀_ : Coverage) {w : 𝕎·} {g : wPred {l} w} (h : Σ∈𝔹 _◀_ g) (f : wPredDep g) → Set (lsuc n ⊔ lsuc m ⊔ l)
Σ∈𝔹' _◀_ {w} {g} (b , f∈b) f =
  {w1 : 𝕎·} (e1 : w ⊑· w1) (ib : w1 ∈· (𝔹.U b)) → Σ (𝔹 _◀_ w1) (λ b' → ∈𝔹Dep b' (f∈b e1 ib) (↑wPredDep'' f e1))
{-# INLINE Σ∈𝔹' #-}

{-- Intersection --}
Coverage∩ : Coverage → Set (lsuc n ⊔ m)
Coverage∩ _◀_ = {w : 𝕎·} (U V : UCSubset) → w ◀ U → w ◀ V → w ◀ (U ⋒ V)

𝔹∩ : {_◀_ : Coverage} (isect : Coverage∩ _◀_) {w : 𝕎·} → 𝔹 _◀_ w → 𝔹 _◀_ w → 𝔹 _◀_ w
𝔹∩ {B} isect {w} (mk𝔹 U w◀U Uext) (mk𝔹 V w◀V Vext) = mk𝔹 bar bars ext
  where
    bar : UCSubset
    bar = U ⋒ V

    bars : B w bar
    bars = isect U V w◀U w◀V

    ext : {w' : 𝕎·} → w' ∈· bar → w ⊑· w'
    ext {w'} (w'∈U , w'∈V) = Uext  w'∈U

{-- Monotonicity --}
res≥ : 𝕎· → UCSubset → UCSubset
res≥ w0 (U , U-UC) = (λ w1 → w1 ∈ U × w0 ⊑· w1)
                   , (λ e12 (w1∈U , e01) → U-UC e12 w1∈U , ⊑-trans· e01 e12)

Coverage⊑ : Coverage → Set (lsuc n ⊔ m)
Coverage⊑ _◀_ =
  {w1 w2 : 𝕎·} (e : w1 ⊑· w2) (U : UCSubset)
  → w1 ◀ U
  → w2 ◀ res≥ w2 U

𝔹⊑ : {_◀_ : Coverage} → Coverage⊑ _◀_ → {w1 w2 : 𝕎·} → w1 ⊑· w2 → 𝔹 _◀_ w1 → 𝔹 _◀_ w2
𝔹⊑ {_◀_} mon {w1} {w2} w1⊑w2 (mk𝔹 U w1◀U Uext) = mk𝔹 bar bars ext
  where
    bar : UCSubset
    bar = res≥ w2 U

    bars : w2 ◀ bar
    bars = mon w1⊑w2 U w1◀U

    ext : {w3 : 𝕎·} → w3 ∈· bar → w2 ⊑· w3
    ext {w3} (w3∈U , w2⊑w3) = w2⊑w3

{-- Top --}
bar∀ : 𝕎· → UCSubset
bar∀ w0 = w0 ⊑·_ , λ e12 e01 → ⊑-trans· e01 e12

Coverage∀ : Coverage → Set (n ⊔ m)
Coverage∀ _◀_ = (w : 𝕎·) → w ◀ (bar∀ w)

𝔹∀ : {_◀_ : Coverage} → Coverage∀ _◀_ → (w : 𝕎·) → 𝔹 _◀_ w
𝔹∀ {B} all w = mk𝔹 bar bars ext
  where
    bar : UCSubset
    bar = bar∀ w

    bars : B w bar
    bars = all w

    ext : {w' : 𝕎·} → w' ∈· bar → w ⊑· w'
    ext {w'} b = b

{-- Union --}
record 𝔹In {_◀_ : Coverage} {w : 𝕎·} (b : 𝔹 _◀_ w) : Set n where
  constructor mk𝔹In
  field
    wi   : 𝕎·
    wi∈U : wi ∈· 𝔹.U b

bar∪ : ∀ {l} {_◀_ : Coverage} {w : 𝕎·} (b : 𝔹 _◀_ w)
       (G : (ind : 𝔹In b) → 𝔹 _◀_ (𝔹In.wi ind) → Set l)
       (i : (ind : 𝔹In b) → Σ[ b ∈ 𝔹 _◀_ (𝔹In.wi ind)] G ind b)
       → UCSubset
bar∪ b G i = ⋓[ ind ∈ 𝔹In b ] 𝔹.U (fst (i ind))

Coverage∪ : Coverage → Setω
Coverage∪ _◀_ =
  ∀ {l} {w : 𝕎·} (b : 𝔹 _◀_ w)
  (G : (ind : 𝔹In b) → 𝔹 _◀_ (𝔹In.wi ind) → Set l)
  (i : (ind : 𝔹In b) → Σ[ b ∈ 𝔹 _◀_ (𝔹In.wi ind)] G ind b)
  → w ◀ (bar∪ b G i)

𝔹∪ : ∀ {l} {_◀_ : Coverage} (fam : Coverage∪ _◀_) {w : 𝕎·} (b : 𝔹 _◀_ w)
     (G : (ind : 𝔹In b) → 𝔹 _◀_ (𝔹In.wi ind) → Set l)
     (i : (ind : 𝔹In b) → Σ[ b ∈ 𝔹 _◀_ (𝔹In.wi ind)] G ind b)
     → 𝔹 _◀_ w
𝔹∪ {_} {_◀_} fam {w} b G i = mk𝔹 bar bars ext
  where
    bar : UCSubset
    bar = bar∪ b G i

    bars : w ◀ bar
    bars = fam b G i

    ext  : {w' : 𝕎·} → w' ∈· bar → w ⊑· w'
    ext {w'} (ind , w'∈iind) = ⊑-trans· (𝔹.ext b (𝔹In.wi∈U ind)) (𝔹.ext (fst (i ind)) w'∈iind)

{-- Inhabitation --}
Coverage∃ : Coverage → Set (lsuc n ⊔ m)
Coverage∃ _◀_ = {w : 𝕎·} {U : UCSubset} → w ◀ U → Σ[ w' ∈ 𝕎· ] w' ∈· U

---- Consequences of the above

↑Σ∈𝔹 : ∀ {l} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) {w : 𝕎·} {f : wPred {l} w} (i : Σ∈𝔹 _◀_ f) {w' : 𝕎·} (e : w ⊑· w') → Σ∈𝔹 _◀_ (↑wPred f e)
↑Σ∈𝔹 mon {w0} {f} (b , i) {w1} e01 = 𝔹⊑ mon e01 b , j
  where
    j : ∈𝔹 (𝔹⊑ mon e01 b) (↑wPred f e01)
    j {w2} e12 (w2∈U , _) w3 e23 e13 = i (𝔹.ext b w2∈U) w2∈U w3 e23 (⊑-trans· e01 e13)


↑'Σ∈𝔹 : ∀ {l} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) {w : 𝕎·} {f : wPred {l} w} (i : Σ∈𝔹 _◀_ f) {w' : 𝕎·} (e : w ⊑· w') → Σ∈𝔹 _◀_ (↑wPred' f e)
↑'Σ∈𝔹 mon {w0} {f} (b , i) {w1} e01 = 𝔹⊑ mon e01 b , j
  where
    j : ∈𝔹 (𝔹⊑ mon e01 b) (↑wPred' f e01)
    j {w2} e12 (w2∈U , _) w3 e23 e13 e03 = i (𝔹.ext b w2∈U) w2∈U w3 e23 e03


↑Σ∈𝔹' : ∀ {l} {_◀_ : Coverage}  (mon : Coverage⊑ _◀_) {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} (i : Σ∈𝔹 _◀_ f) {w' : 𝕎·} (e : w ⊑· w')
      → Σ∈𝔹' _◀_ i g → Σ∈𝔹' _◀_ (↑Σ∈𝔹 mon i e) (↑wPredDep g e)
↑Σ∈𝔹' mon {w0} {f} {g} i {w1} e01 j {w2} e12 (w2∈U , e12') =
  fst (j (𝔹.ext (fst i) w2∈U) w2∈U) , k
  where
    k : ∈𝔹Dep (fst (j (𝔹.ext (fst i) w2∈U) w2∈U))
              (snd (↑Σ∈𝔹 mon i e01) e12 (w2∈U , e12'))
              (↑wPredDep'' (↑wPredDep g e01) e12)
    k {w3} e23 w3∈j w4 e34 e24 e14 = snd (j (𝔹.ext (fst i) w2∈U) w2∈U) e23 w3∈j w4 e34 e24 (⊑-trans· e01 e14)


Σ∈𝔹Func : ∀ {l r} {_◀_ : Coverage} (isect : Coverage∩ _◀_) {w : 𝕎·} {f : wPred {l} w} {g : wPred {r} w}
          → Σ∈𝔹 _◀_ (λ w' e' → f w' e' → g w' e')
          → Σ∈𝔹 _◀_ f → Σ∈𝔹 _◀_ g
Σ∈𝔹Func isect {w0} {f} {g} (b1 , i1) (b2 , i2) =
  𝔹∩ isect b1 b2 , i
  where
    i : ∈𝔹 (𝔹∩ isect b1 b2) g
    i {w1} e01 (w1∈U1 , w1∈U2) w2 w12 e02 = i1 (𝔹.ext b1 w1∈U1) w1∈U1 w2 w12 e02 (i2 (𝔹.ext b2 w1∈U2) w1∈U2 w2 w12 e02)


∀𝕎-Σ∈𝔹Func : ∀ {l r} {_◀_ : Coverage} {w : 𝕎·} {f : wPred {l} w} {g : wPred {r} w}
              → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
              → Σ∈𝔹 _◀_ f → Σ∈𝔹 _◀_ g
∀𝕎-Σ∈𝔹Func {_} {_} {_◀_} {w} {f} {g} aw (b , i) = b , j
  where
    j : ∈𝔹 b g
    j e b' w' e' z = aw w' z (i (𝔹.ext b b') b' w' e' z)


∀𝕎-Σ∈𝔹 : ∀ {l} {_◀_ : Coverage} (all : Coverage∀ _◀_) {w : 𝕎·} {f : wPred {l} w} → ∀𝕎 w f → Σ∈𝔹 _◀_ f
∀𝕎-Σ∈𝔹 {_} {_◀_} all {w} {f} h = 𝔹∀ all w , i
  where
    i : ∈𝔹 {_} {_◀_} (𝔹∀ all w) f
    i {w'} e b w1 e1 z = h w1 z


Σ∈𝔹-Σ∈𝔹' : ∀ {l} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f}
             → Σ∈𝔹 _◀_ (λ w' e' → (x : f w' e') → g w' e' x)
             → (i : Σ∈𝔹 _◀_ f) → Σ∈𝔹' _◀_ i g
Σ∈𝔹-Σ∈𝔹' mon {w0} {f} {g} (b1 , i1) (b2 , i2) {w1} e01 w1∈b2 =
  𝔹⊑ mon e01 b1 , j
  where
    j : ∈𝔹Dep (𝔹⊑ mon e01 b1) (i2 e01 w1∈b2) (↑wPredDep'' g e01)
    j {w2} e12 (w2∈b1 , _) w3 e23 e13 e03 = i1 (𝔹.ext b1 w2∈b1) w2∈b1 w3 e23 e03 (i2 e01 w1∈b2 w3 e13 e03)


∀𝕎-Σ∈𝔹-Σ∈𝔹' : ∀ {l} {_◀_ : Coverage} (all : Coverage∀ _◀_) {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} (i : Σ∈𝔹 _◀_ f)
                → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : at_◀_eth_◀_ar i w' e' x)--} → g w' e' x)
                → Σ∈𝔹' _◀_ i g
∀𝕎-Σ∈𝔹-Σ∈𝔹' {l} {_◀_} all {w} {f} {g} (b , i) aw {w'} e ib =
  𝔹∀ all w' , j
  where
    j : ∈𝔹Dep {_} {_◀_} (𝔹∀ all w') (i e ib) (↑wPredDep'' g e)
    j {w0} e0 ib' w1 e1 x y = aw w1 y (i e ib w1 x y)


bar-𝔹⊑→ : {_◀_ : Coverage} (mon : Coverage⊑ _◀_) {w w' : 𝕎·} (e : w ⊑· w') {b : 𝔹 _◀_ w} {w0 : 𝕎·}
            → w0 ∈· 𝔹.U (𝔹⊑ mon e b)
            → w0 ∈· 𝔹.U b
bar-𝔹⊑→ mon {w0} {w1} e01 {b} {w2} (w2∈b , _) = w2∈b


Σ∈𝔹'-comb-change : ∀ {l r s} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) (isect : Coverage∩ _◀_) (fam : Coverage∪ _◀_)
                    {w : 𝕎·} {f₁ : wPred {l} w} {f₂ : wPred {r} w} {f₃ : wPred {s} w}
                    {g₁ : wPredDep f₁} {g₂ : wPredDep f₂} {g₃ : wPredDep f₃}
                    (i₁ : Σ∈𝔹 _◀_ f₁) (i₂ : Σ∈𝔹 _◀_ f₂) (i₃ : Σ∈𝔹 _◀_ f₃)
                    → ∀𝕎 w (λ w' e' → (x₁ : f₁ w' e') (x₂ : f₂ w' e') (x₃ : f₃ w' e')
                                     → g₁ w' e' x₁ → g₂ w' e' x₂ → g₃ w' e' x₃)
                    → Σ∈𝔹' _◀_ i₁ g₁ → Σ∈𝔹' _◀_ i₂ g₂ → Σ∈𝔹' _◀_ i₃ g₃
Σ∈𝔹'-comb-change {_} {_} {_} {_◀_} mon isect fam {w} {f₁} {f₂} {f₃} {g₁} {g₂} {g₃} (b₁ , i₁) (b₂ , i₂) (b₃ , i₃) aw z₁ z₂ {w'} e ib =
  𝔹∩ isect b1 b2 , j
  where
    z₁' : (ind : 𝔹In (𝔹⊑ mon e b₁))
          → Σ (𝔹 _◀_ (𝔹In.wi ind)) (λ b' → ∈𝔹Dep b' (i₁ (𝔹.ext b₁ (fst (𝔹In.wi∈U ind))) (fst (𝔹In.wi∈U ind))) (↑wPredDep'' g₁ (𝔹.ext b₁ (fst (𝔹In.wi∈U ind)))))
    z₁' (mk𝔹In wi (wi∈b₁ , e')) = z₁ (𝔹.ext b₁ wi∈b₁) wi∈b₁

    b1 : 𝔹 _◀_ w'
    b1 = 𝔹∪ fam (𝔹⊑ mon e b₁)
                (λ (mk𝔹In wi (wi∈b₁ , e')) b' → ∈𝔹Dep b' (i₁ (𝔹.ext b₁ wi∈b₁) wi∈b₁) (↑wPredDep'' g₁ (𝔹.ext b₁ wi∈b₁)))
                z₁'

    z₂' : (ind : 𝔹In (𝔹⊑ mon e b₂))
          → Σ (𝔹 _◀_ (𝔹In.wi ind)) (λ b' → ∈𝔹Dep b' (i₂ (𝔹.ext b₂ (fst (𝔹In.wi∈U ind))) (fst (𝔹In.wi∈U ind))) (↑wPredDep'' g₂ (𝔹.ext b₂ (fst (𝔹In.wi∈U ind)))))
    z₂' (mk𝔹In wi (wi∈b₂ , e')) = z₂ (𝔹.ext b₂ wi∈b₂) wi∈b₂

    b2 : 𝔹 _◀_ w'
    b2 = 𝔹∪ fam (𝔹⊑ mon e b₂)
                (λ (mk𝔹In wi (wi∈b₂ , e')) b' → ∈𝔹Dep b' (i₂ (𝔹.ext b₂ wi∈b₂) wi∈b₂) (↑wPredDep'' g₂ (𝔹.ext b₂ wi∈b₂)))
                z₂'

    j : ∈𝔹Dep (𝔹∩ isect b1 b2) (i₃ e ib) (↑wPredDep'' g₃ e)
    j e2 ((mk𝔹In w1 (w1∈b₁ , e4) , w''∈U1) , (mk𝔹In w2 (w2∈b₂ , e5) , w''∈U2)) w3 e3 x x₁ =
      aw w3 x₁
        (i₁ (𝔹.ext b₁ w1∈b₁) w1∈b₁ w3 (⊑-trans· (𝔹.ext (fst (z₁' (mk𝔹In w1 (w1∈b₁ , e4)))) w''∈U1) e3) x₁)
        (i₂ (𝔹.ext b₂ w2∈b₂) w2∈b₂ w3 (⊑-trans· (𝔹.ext (fst (z₂' (mk𝔹In w2 (w2∈b₂ , e5)))) w''∈U2) e3) x₁)
        (i₃ e ib w3 x x₁)
        (snd (z₁' (mk𝔹In w1 (w1∈b₁ , e4))) (𝔹.ext (fst (z₁' (mk𝔹In w1 (w1∈b₁ , e4)))) w''∈U1) w''∈U1 w3 e3 ((⊑-trans· (𝔹.ext (fst (z₁' (mk𝔹In w1 (w1∈b₁ , e4)))) w''∈U1) e3)) x₁)
        (snd (z₂' (mk𝔹In w2 (w2∈b₂ , e5))) (𝔹.ext (fst (z₂' (mk𝔹In w2 (w2∈b₂ , e5)))) w''∈U2) w''∈U2 w3 e3 ((⊑-trans· (𝔹.ext (fst (z₂' (mk𝔹In w2 (w2∈b₂ , e5)))) w''∈U2) e3)) x₁)

Σ∈𝔹-idem-aux : ∀ {l} {_◀_ : Coverage} (fam : Coverage∪ _◀_) {w : 𝕎·} {f : wPred {l} w}
                → (b : 𝔹 _◀_ w)
                → (i : ∈𝔹 b (λ w' e' → Σ∈𝔹 _◀_ (↑wPred' f e')))
                → Σ∈𝔹 _◀_ f
Σ∈𝔹-idem-aux fam {w} {f} b i =
  𝔹∪ fam {w} b G k , j
  where
    G = λ (mk𝔹In wi wi∈b) bw → ∈𝔹 bw (↑wPred' f (𝔹.ext b wi∈b))
    k = λ (mk𝔹In wi wi∈b) → i (𝔹.ext b wi∈b) wi∈b wi (⊑-refl· _) (𝔹.ext b wi∈b)

    j : ∈𝔹 (𝔹∪ fam b G k) f
    j {w1} e (mk𝔹In wi wi∈b , w1∈bi) w2 e12 e2 =
      snd (i (𝔹.ext b wi∈b) wi∈b wi (⊑-refl· wi) (𝔹.ext b wi∈b))
        (𝔹.ext (fst (k (mk𝔹In wi wi∈b))) w1∈bi)
        w1∈bi w2 e12
        (⊑-trans· (𝔹.ext (fst (k (mk𝔹In wi wi∈b))) w1∈bi) e12)
        e2


Σ∈𝔹-idem : ∀ {l} {_◀_ : Coverage} (fam : Coverage∪ _◀_) {w : 𝕎·} {f : wPred {l} w}
            → Σ∈𝔹 _◀_ (λ w' e' → Σ∈𝔹 _◀_ (↑wPred' f e'))
            → Σ∈𝔹 _◀_ f
Σ∈𝔹-idem fam {w} {f} (b , i) = Σ∈𝔹-idem-aux fam b i


Σ∈𝔹'-idem : ∀ {l} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) (fam : Coverage∪ _◀_)
             {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} (i : Σ∈𝔹 _◀_ f)
             → Σ∈𝔹 _◀_ (λ w' e' → Σ∈𝔹' _◀_ (↑'Σ∈𝔹 mon i e') (↑wPredDep' g e'))
             → Σ∈𝔹' _◀_ i g
Σ∈𝔹'-idem {l} {_◀_} mon fam {w} {f} {g} (b₁ , i) (b₂ , j) {w'} e ib =
  𝔹∪ fam (𝔹⊑ mon e b₂) G k , jd
  where
    G = λ (mk𝔹In wi (wi∈b₂ , e'i)) bi → ∈𝔹Dep bi (λ w2 e2 z' y' → i e ib _ (⊑-trans· e'i e2) y') (↑wPredDep'' (↑wPredDep' g (⊑-trans· e e'i)) (⊑-refl· _))
    k = λ (mk𝔹In wi (wi∈b₂ , e'i)) → j (𝔹.ext b₂ wi∈b₂) wi∈b₂ wi (⊑-refl· wi) (⊑-trans· e e'i) (⊑-refl· wi) (snd (𝔹.U b₁) e'i ib , ⊑-refl· wi)

    jd : ∈𝔹Dep (𝔹∪ fam (𝔹⊑ mon e b₂) G k) (i e ib) (↑wPredDep'' g e)
    jd {w0} e₁ (mk𝔹In wi (wi∈b₂ , e'i) , w0∈ki) w1 e01 e'1 e1 =
      snd (j (𝔹.ext b₂ wi∈b₂) wi∈b₂ wi (⊑-refl· wi) (⊑-trans· e e'i) (⊑-refl· wi) (snd (𝔹.U b₁) e'i ib , ⊑-refl· wi))
        (𝔹.ext (fst (j (𝔹.ext b₂ wi∈b₂) wi∈b₂ wi (⊑-refl· wi) (⊑-trans· e e'i) (⊑-refl· wi) (snd (𝔹.U b₁) e'i ib , ⊑-refl· wi))) w0∈ki)
        w0∈ki w1 e01
        (⊑-trans· (𝔹.ext (fst (j (𝔹.ext b₂ wi∈b₂) wi∈b₂ wi (⊑-refl· wi) (⊑-trans· e e'i) (⊑-refl· wi) (snd (𝔹.U b₁) e'i ib , ⊑-refl· wi))) w0∈ki) e01)
        (⊑-trans· (𝔹.ext (fst (j (𝔹.ext b₂ wi∈b₂) wi∈b₂ wi (⊑-refl· wi) (⊑-trans· e e'i) (⊑-refl· wi) (snd (𝔹.U b₁) e'i ib , ⊑-refl· wi))) w0∈ki) e01)
        e1 (i e ib w1 e'1 e1)


∀𝕎-Σ∈𝔹'-Σ∈𝔹-aux : ∀ {l r} {_◀_ : Coverage} (fam : Coverage∪ _◀_)
                     {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} {h : wPred {r} w} -- TODO: is using both l and r correct?
                     (b : 𝔹 _◀_ w)
                     (i : ∈𝔹 b f)
                     → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                     → Σ∈𝔹' _◀_ (b , i) g → Σ∈𝔹 _◀_ h
∀𝕎-Σ∈𝔹'-Σ∈𝔹-aux fam {w} {f} {g} {h} b i aw j =
  𝔹∪ fam b G k , i'
  where
    G = λ (mk𝔹In wi wi∈b) bi → ∈𝔹Dep bi (i (𝔹.ext b wi∈b) wi∈b) (↑wPredDep'' g (𝔹.ext b wi∈b))
    k = λ (mk𝔹In wi wi∈b) → j (𝔹.ext b wi∈b) wi∈b

    i' : ∈𝔹 (𝔹∪ fam b G k) h
    i' {w'} e (mk𝔹In wi wi∈b , F) w1 e1 z =
      aw w1 z
         (i (𝔹.ext b wi∈b) wi∈b w1 (⊑-trans· (𝔹.ext (proj₁ (j (𝔹.ext b wi∈b) wi∈b)) F) e1) z)
         (snd (j (𝔹.ext b wi∈b) wi∈b)
              (𝔹.ext (proj₁ (j (𝔹.ext b wi∈b) wi∈b)) F)
              F w1 e1
              (⊑-trans· (𝔹.ext (proj₁ (j (𝔹.ext b wi∈b) wi∈b)) F) e1)
              z)


∀𝕎-Σ∈𝔹'-Σ∈𝔹 : ∀ {l r} {_◀_ : Coverage} (fam : Coverage∪ _◀_)
                 {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} {h : wPred {r} w} (i : Σ∈𝔹 _◀_ f)
                 → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                 → Σ∈𝔹' _◀_ i g → Σ∈𝔹 _◀_ h
∀𝕎-Σ∈𝔹'-Σ∈𝔹 fam (b , i) aw j = ∀𝕎-Σ∈𝔹'-Σ∈𝔹-aux fam b i aw j


∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem-aux : ∀ {l r} {_◀_ : Coverage} (fam : Coverage∪ _◀_)
                          {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} {h : wPred {r} w}
                          (b : 𝔹 _◀_ w)
                          (i : ∈𝔹 b f)
                          → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → Σ∈𝔹 _◀_ (↑wPred' h e'))
                          → Σ∈𝔹' _◀_ (b , i) g → Σ∈𝔹 _◀_ h
∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem-aux fam {w} {f} {g} {h} b i aw j =
  𝔹∪ fam b G k ,
  λ {w'} e (mk𝔹In w1 ib , (mk𝔹In w3 br , ib2)) w2 e2 z →
    let e1 = 𝔹.ext b ib
        e3 = 𝔹.ext (fst (j e1 ib)) br
     in snd (aw w3 (⊑-trans· e1 e3) (i e1 ib w3 e3 (⊑-trans· e1 e3)) (snd (j e1 ib) e3 br w3 (⊑-refl· w3) e3 (⊑-trans· e1 e3)))
            (𝔹.ext(proj₁ (aw w3 (⊑-trans· e1 e3) (i e1 ib w3 e3 (⊑-trans· e1 e3)) (snd (j e1 ib) e3 br w3 (⊑-refl· w3) e3 (⊑-trans· e1 e3)))) ib2)
            ib2 w2 e2 ((⊑-trans· (𝔹.ext (fst (aw w3 (⊑-trans· e1 e3) (i e1 ib w3 e3 (⊑-trans· e1 e3)) (snd (j e1 ib) e3 br w3 (⊑-refl· w3) e3 (⊑-trans· e1 e3)))) ib2) e2)) z
  where
    G = λ (mk𝔹In wi wi∈b) bi → ∈𝔹 bi (↑wPred' h (𝔹.ext b wi∈b))
    k = λ (mk𝔹In wi wi∈b) →
      let ei = 𝔹.ext b wi∈b
          b' , g∈b' = j ei wi∈b
          G' = λ (mk𝔹In wj wj∈b') bj → ∈𝔹 bj (↑wPred' h (⊑-trans· ei (𝔹.ext b' wj∈b')))
          k' = λ (mk𝔹In wj wj∈b') → aw wj (⊑-trans· ei (𝔹.ext b' wj∈b')) (i ei wi∈b wj  (𝔹.ext b' wj∈b') (⊑-trans· ei (𝔹.ext b' wj∈b'))) (g∈b' (𝔹.ext b' wj∈b') wj∈b' wj (⊑-refl· wj) (𝔹.ext b' wj∈b') (⊑-trans· ei (𝔹.ext b' wj∈b')))
       in 𝔹∪ fam b' G' k' ,
         λ {w1} e1 (mk𝔹In w3 w3∈b' , w1∈bj) w2 e2 e32 → let e3 = 𝔹.ext b' w3∈b' in
           snd (aw w3 (⊑-trans· ei e3) (i ei wi∈b w3 e3 (⊑-trans· ei e3)) (snd (j ei wi∈b) e3 w3∈b' w3 (⊑-refl· w3) e3 (⊑-trans· ei e3)))
               (𝔹.ext (fst (aw w3 (⊑-trans· ei e3) (i ei wi∈b w3 e3 (⊑-trans· ei e3)) (snd (j ei wi∈b) e3 w3∈b' w3 (⊑-refl· w3) e3 (⊑-trans· ei e3)))) w1∈bj)
               w1∈bj w2 e2 (⊑-trans· (𝔹.ext (fst (aw w3 (⊑-trans· ei e3) (i ei wi∈b w3 e3 (⊑-trans· ei e3)) (snd (j ei wi∈b) e3 w3∈b' w3 (⊑-refl· w3) e3 (⊑-trans· ei e3)))) w1∈bj) e2)
{-# INLINE ∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem-aux #-}


∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem : ∀ {l r} {_◀_ : Coverage} (fam : Coverage∪ _◀_)
                     {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} {h : wPred {r} w}
                     (b : Σ∈𝔹 _◀_ f)
                     → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → Σ∈𝔹 _◀_ (↑wPred' h e'))
                     → Σ∈𝔹' _◀_ b g → Σ∈𝔹 _◀_ h
∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem fam (b , i) aw j = ∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem-aux fam b i aw j
{-# INLINE ∀𝕎-Σ∈𝔹'-Σ∈𝔹-idem #-}

-- This really only need isect, but can conveniently be derived from Σ∈𝔹'-comb-change
Σ∈𝔹'-comb : ∀ {l} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) (isect : Coverage∩ _◀_) (fam : Coverage∪ _◀_)
             {w : 𝕎·} {f : wPred {l} w} {g h k : wPredDep f} (i : Σ∈𝔹 _◀_ f)
             → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                              → g w' e' zg → h w' e' zh → k w' e' z)
             → Σ∈𝔹' _◀_ i g → Σ∈𝔹' _◀_ i h → Σ∈𝔹' _◀_ i k
Σ∈𝔹'-comb {l} {_◀_} mon isect fam {w} {f} {g} {h} {k} i aw j₁ j₂ =
  Σ∈𝔹'-comb-change {l} {l} {l} {_◀_} mon isect fam {w} {f} {f} {f} {g} {h} {k}
                    i i i (λ w1 e1 x₁ x₂ x₃ a b → aw w1 e1 x₃ x₁ x₂ a b) j₁ j₂

-- This really only needs mon and fam, but can conveniently be derived from Σ∈𝔹'-comb-change
Σ∈𝔹'-change : ∀ {l} {_◀_ : Coverage} (mon : Coverage⊑ _◀_) (isect : Coverage∩ _◀_) (fam : Coverage∪ _◀_)
               {w : 𝕎·} {f k : wPred {l} w} {g : wPredDep f} {h : wPredDep k}
               (i : Σ∈𝔹 _◀_ f) (j : Σ∈𝔹 _◀_ k)
               → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e')
                                → g w' e' x → h w' e' y)
               → Σ∈𝔹' _◀_ i g → Σ∈𝔹' _◀_ j h
Σ∈𝔹'-change {_} {_◀_} mon isect fam {w} {f} {k} {g} {h} i j aw z =
  Σ∈𝔹'-comb-change mon isect fam {w} {f} {f} {k} {g} {g} {h} i i j (λ w1 e1 x₁ x₂ x₃ a b → aw w1 e1 x₁ x₃ a) z z


Σ∈𝔹-const : ∀ {l} {B : Coverage} (ex : Coverage∃ B) {w : 𝕎·} {t : Set l} → Σ∈𝔹 B {w} (λ w e → t) → t --TODO: Check if l is correct instead of n
Σ∈𝔹-const {_} {B} ex {w} {t} (b , i) =
  let w' , w'∈b = ex (𝔹.covers b)
   in i (𝔹.ext b w'∈b ) w'∈b w' (⊑-refl· w') (𝔹.ext b w'∈b )


Σ∈𝔹→∃ : ∀ {l} {B : Coverage} (ex : Coverage∃ B) {w : 𝕎·} {f : wPred {l} w} → Σ∈𝔹 B {w} f → ∃𝕎 w λ w' e → f w' e
Σ∈𝔹→∃ {_} {B} ex {w} {f} (b , i) =
  let w' , w'∈b = ex (𝔹.covers b)
   in w' , 𝔹.ext b w'∈b , i (𝔹.ext b w'∈b ) w'∈b w' (⊑-refl· w') (𝔹.ext b w'∈b )


-- TODO: is this derivable from the others?
→Σ∈𝔹∀𝕎 : ∀ {l} {_◀_ : Coverage} {w : 𝕎·} {f : wPred {l} w}
            → Σ∈𝔹 _◀_ f
            → Σ∈𝔹 _◀_ (λ w' e → ∀𝕎 w' (↑wPred f e))
→Σ∈𝔹∀𝕎 {_} {_} {w} {f} (b , i) = b , j
  where
    j : ∈𝔹 b (λ w' e → ∀𝕎 w' (↑wPred f e))
    j {w'} e b w1 e1 z w2 e2 = i e b w2 (⊑-trans· e1 e2) (⊑-trans· z e2)


{-- Those are all the properties we need about Bars to derive the above properties,
    which in turn are the properties of Bar below.
    We show 2 intances below:
    (1) O𝔹BarsProps for open bars
    (2) IS𝔹BarsProps for Beth Bars
 --}
-- bars are the open sets of a topological space equipped with the set of 𝕎
record CoverageProps : Setω where
  constructor mkCoverageProps
  field
    bars  : Coverage
    mon   : Coverage⊑ bars
    isect : Coverage∩ bars
    all   : Coverage∀ bars
    fam   : Coverage∪ bars
    ex    : Coverage∃ bars
\end{code}
