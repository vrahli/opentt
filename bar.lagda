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


module bar {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)




{-----------------------------------------
 --
 -- Generic bar type
 --
 --}


Br : Set(lsuc(L))
Br = 𝕎· → Set(L)


Bars : Set(lsuc(lsuc(L)))
Bars = 𝕎· → Br → Set(lsuc(L))


record 𝔹 (B : Bars) (w : 𝕎·) : Set(lsuc(L)) where
  constructor mk𝔹
  field
    bar  : Br
    bars : B w bar
    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    mon  : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2


{-- Bars and dependent bars --}
∈𝔹 : {B : Bars} {w : 𝕎·}  (b : 𝔹 B w) (f : wPred w) → Set(lsuc(L))
∈𝔹 {B} {w} b f = {w' : 𝕎·} (e : w ⊑· w') → 𝔹.bar b w' → ∀𝕎 w' (↑wPred' f e)
{-# INLINE ∈𝔹 #-}


Σ∈𝔹 : (B : Bars) {w : 𝕎·} (f : wPred w) → Set(lsuc(L))
Σ∈𝔹 B {w} f = Σ (𝔹 B w) (λ b → ∈𝔹 b f)
{-# INLINE Σ∈𝔹 #-}


∈𝔹Dep : {B : Bars} {w : 𝕎·} (b : 𝔹 B w) {g : wPred w} (i : ∀𝕎 w g) (f : wPredDep g) → Set(lsuc(L))
∈𝔹Dep {B} {w} b {g} i f =
  {w' : 𝕎·} (e : w ⊑· w') → 𝔹.bar b w'
  → ∀𝕎 w' (λ w'' e' → (x : w ⊑· w'') → f w'' x (i w'' x))
{-# INLINE ∈𝔹Dep #-}


Σ∈𝔹' : (B : Bars) {w : 𝕎·} {g : wPred w} (h : Σ∈𝔹 B g) (f : wPredDep g) → Set(lsuc(L))
Σ∈𝔹' B {w} {g} bi f =
  {w1 : 𝕎·} (e1 : w ⊑· w1) (ib : 𝔹.bar (fst bi) w1)
  → Σ (𝔹 B w1) (λ b' → ∈𝔹Dep b' (snd bi e1 ib) (↑wPredDep'' f e1))
{-# INLINE Σ∈𝔹' #-}


{-- Intersection --}
bar∩ : Br → Br → Br
bar∩ b1 b2 w0 = Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → b1 w1 × b2 w2 × w1 ⊑· w0 × w2 ⊑· w0))


Bars∩ : (B : Bars) → Set(lsuc(L))
Bars∩ B =
  {w : 𝕎·} (b1 b2 : Br)
  → B w b1
  → B w b2
  → B w (bar∩ b1 b2)


∩𝔹 : {B : Bars} (isect : Bars∩ B) {w : 𝕎·} → 𝔹 B w → 𝔹 B w → 𝔹 B w
∩𝔹 {B} isect {w} (mk𝔹 b1 bars1 ext1 mon1) (mk𝔹 b2 bars2 ext2 mon2) =
  mk𝔹 bar bars ext mon
  where
    bar : Br
    bar = bar∩ b1 b2

    bars : B w bar
    bars = isect b1 b2 bars1 bars2

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (w1 , w2 , b₁ , b₂ , e₁ , e₂) = ⊑-trans· (𝔹.ext {B} {w} (mk𝔹 b1 bars1 ext1 mon1) {w1} b₁) e₁

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (wa , wb , ba , bb , ea , eb) = wa , wb , ba , bb , ⊑-trans· ea e , ⊑-trans· eb e



{-- Monotonicity --}
bar⊑ : 𝕎· → Br → Br
bar⊑ w' bar w0 = Σ 𝕎· (λ w1 → bar w1 × w1 ⊑· w0 × w' ⊑· w0)


Bars⊑ : (B : Bars) → Set(lsuc(L))
Bars⊑ B =
  {w1 w2 : 𝕎·} (e : w1 ⊑· w2) (bar : Br)
  → B w1 bar
  → B w2 (bar⊑ w2 bar)


𝔹⊑ : {B : Bars} (mon : Bars⊑ B) {w w' : 𝕎·} (e : w ⊑· w') → 𝔹 B w → 𝔹 B w'
𝔹⊑ {B} MB {w} {w'} e (mk𝔹 bar bars ext mon) = mk𝔹 bar' bars' ext' mon'
  where
    bar' : Br
    bar' = bar⊑ w' bar

    bars' : B w' bar'
    bars' = MB e bar bars

    ext' : {w'' : 𝕎·} → bar' w'' → w' ⊑· w''
    ext' {w''} (w1 , b , e₁ , e₂) = e₂

    mon' : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar' w1 → bar' w2
    mon' {w1} {w2} e (w0 , b0 , e₁ , e₂) = w0 , b0 , ⊑-trans· e₁ e , ⊑-trans· e₂ e



{-- Top --}
bar∀ : 𝕎· → Br
bar∀ w w' = w ⊑· w'


Bars∀ : (B : Bars) → Set(lsuc(L))
Bars∀ B = (w : 𝕎·) → B w (bar∀ w)


𝔹∀ : {B : Bars} (all : Bars∀ B) (w : 𝕎·) → 𝔹 B w
𝔹∀ {B} all w =
  mk𝔹 bar bars ext mon
  where
    bar : Br
    bar = bar∀ w

    bars : B w bar
    bars = all w

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} b = b

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e b = ⊑-trans· b e


{--
{-- Families(1) --}
record 𝔹Fam {B : Bars} {w : 𝕎·} (b : 𝔹 B w) : Set(L) where
  constructor mk𝔹Fam
  field
    w1 : 𝕎·
    e1 : w ⊑· w1
    br : 𝔹.bar b w1
    w2 : 𝕎·
    e2 : w1 ⊑· w2
    z  : w ⊑· w2


barFam : {B : Bars} {w : 𝕎·} (b : 𝔹 B w)
         (G : {w0 : 𝕎·} (e0 : w ⊑· w0) {w1 : 𝕎·} (e1 : w0 ⊑· w1) (z : w ⊑· w1) → 𝔹 B w1 → Set(lsuc(L)))
         (i : {w0 : 𝕎·} (e0 : w ⊑· w0) (ib0 : 𝔹.bar b w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w ⊑· w1)
               → Σ (𝔹 B w1) (λ b' → G e0 e1 z b'))
         → Br
barFam {B} {w} b G i w' = Σ (𝔹Fam b) (λ F → 𝔹.bar (fst (i (𝔹Fam.e1 F) (𝔹Fam.br F) (𝔹Fam.w2 F) (𝔹Fam.e2 F) (𝔹Fam.z F))) w')


BarsFam1 : (B : Bars) → Set(lsuc(lsuc(L)))
BarsFam1 B =
  {w : 𝕎·} (b : 𝔹 B w)
  (G : {w0 : 𝕎·} (e0 : w ⊑· w0) {w1 : 𝕎·} (e1 : w0 ⊑· w1) (z : w ⊑· w1) → 𝔹 B w1 → Set(lsuc(L)))
  (i : {w0 : 𝕎·} (e0 : w ⊑· w0) (ib0 : 𝔹.bar b w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w ⊑· w1)
       → Σ (𝔹 B w1) (λ b' → G e0 e1 z b'))
  → B w (barFam b G i)


-- TODO: check why G is not requiring ib0
-- TODO: check whether the 2nd families are enough since bars are monotonic
-- DONE: Yeap the 2nd family is enough
𝔹fam : {B : Bars} (fam : BarsFam1 B) {w : 𝕎·} (b : 𝔹 B w)
        (G : {w0 : 𝕎·} (e0 : w ⊑· w0) {w1 : 𝕎·} (e1 : w0 ⊑· w1) (z : w ⊑· w1) → 𝔹 B w1 → Set(lsuc(L)))
        (i : {w0 : 𝕎·} (e0 : w ⊑· w0) (ib0 : 𝔹.bar b w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w ⊑· w1)
              → Σ (𝔹 B w1) (λ b' → G e0 e1 z b'))
         → 𝔹 B w
𝔹fam {B} fam {w} b G i = mk𝔹 bar bars ext mon
  where
    bar : Br
    bar = barFam b G i

    bars : B w bar
    bars = fam b G i

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (𝔹Fam.z F) (𝔹.ext (fst (i (𝔹Fam.e1 F) (𝔹Fam.br F) (𝔹Fam.w2 F) (𝔹Fam.e2 F) (𝔹Fam.z F))) b')

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (F , b) = F , 𝔹.mon (fst (i (𝔹Fam.e1 F) (𝔹Fam.br F) (𝔹Fam.w2 F) (𝔹Fam.e2 F) (𝔹Fam.z F))) e b
--}


{-- Union --}
record 𝔹In {B : Bars} {w : 𝕎·} (b : 𝔹 B w) : Set(L) where
  constructor mk𝔹In
  field
    w1 : 𝕎·
    e1 : w ⊑· w1
    br : 𝔹.bar b w1


barFam2 : {B : Bars} {w : 𝕎·} (b : 𝔹 B w)
          (G : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → 𝔹 B w' → Set(lsuc(L)))
          (i : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → Σ (𝔹 B w') (λ b' → G e ib b'))
          → Br
barFam2 {B} {w} b G i w' = Σ (𝔹In b) (λ F → 𝔹.bar (fst (i (𝔹In.e1 F) (𝔹In.br F))) w')


BarsFam2 : (B : Bars) → Set(lsuc(lsuc(L)))
BarsFam2 B =
  {w : 𝕎·} (b : 𝔹 B w)
  (G : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → 𝔹 B w' → Set(lsuc(L)))
  (i : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → Σ (𝔹 B w') (λ b' → G e ib b'))
  → B w (barFam2 b G i)


𝔹fam2 : {B : Bars} (fam : BarsFam2 B) {w : 𝕎·} (b : 𝔹 B w)
         (G : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → 𝔹 B w' → Set(lsuc(L)))
         (i : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → Σ (𝔹 B w') (λ b' → G e ib b'))
         → 𝔹 B w
𝔹fam2 {B} fam {w} b G i = mk𝔹 bar bars ext mon
  where
    bar : Br
    bar = barFam2 b G i

    bars : B w bar
    bars = fam b G i

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (𝔹In.e1 F) (𝔹.ext (fst (i (𝔹In.e1 F) (𝔹In.br F))) b')

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (F , b) = F , 𝔹.mon (fst (i (𝔹In.e1 F) (𝔹In.br F))) e b



{-- Inhabitation --}
Bars∃ : (B : Bars) → Set(lsuc(L))
Bars∃ B =
  {w : 𝕎·} {bar : Br} (bars : B w bar) (ext : {w' : 𝕎·} → bar w' → w ⊑· w')
  → Σ 𝕎· λ w' → Σ (w ⊑· w') λ e → bar w'



---- Consequences of the above

↑Σ∈𝔹 : {B : Bars} (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} (i : Σ∈𝔹 B f) {w' : 𝕎·} (e : w ⊑· w') → Σ∈𝔹 B (↑wPred f e)
↑Σ∈𝔹 {B} mon {w} {f} (b , i) {w'} e = 𝔹⊑ mon e b , j
  where
    j : ∈𝔹 (𝔹⊑ mon e b) (↑wPred f e)
    j {w1} e1 (w0 , b0 , e₁ , e₂) w2 e2 z = i (𝔹.ext b {w0} b0) b0 w2 (⊑-trans· e₁ e2) (⊑-trans· e z)


↑'Σ∈𝔹 : {B : Bars} (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} (i : Σ∈𝔹 B f) {w' : 𝕎·} (e : w ⊑· w') → Σ∈𝔹 B (↑wPred' f e)
↑'Σ∈𝔹 {B} mon {w} {f} (b , i) {w'} e = 𝔹⊑ mon e b , j
  where
    j : ∈𝔹 (𝔹⊑ mon e b) (↑wPred' f e)
    j {w1} e1 (w0 , b0 , e₁ , e₂) w2 e2 z x = i (𝔹.ext b {w0} b0) b0 w2 (⊑-trans· e₁ e2) x




↑Σ∈𝔹' : {B : Bars}  (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 B f) {w' : 𝕎·} (e : w ⊑· w')
         → Σ∈𝔹' B i g → Σ∈𝔹' B (↑Σ∈𝔹 mon i e) (↑wPredDep g e)
↑Σ∈𝔹' {B} mon {w} {f} {g} i {w'} e j {w1} e1 (w2 , b , ea , eb) =
  𝔹⊑ mon ea (fst (j (𝔹.ext (fst i) b) b)) , k
  where
    k : ∈𝔹Dep {B} (𝔹⊑ mon ea (fst (j (𝔹.ext (proj₁ i) b) b)))
                  (snd (↑Σ∈𝔹 mon i e) e1 (w2 , b , ea , eb))
                  (↑wPredDep'' (↑wPredDep g e) e1)
    k {w3} e3 (w3' , b1 , ec , ed) w4 e4 x y =
      snd (j (𝔹.ext (proj₁ i) b) b)
          (𝔹.ext (fst (j (𝔹.ext (proj₁ i) b) b)) b1)
          b1 w4
          (⊑-trans· ec e4) (⊑-trans· ea x) (⊑-trans· e y)


Σ∈𝔹Func : {B : Bars} (isect : Bars∩ B) {w : 𝕎·} {f g : wPred w}
          → Σ∈𝔹 B (λ w' e' → f w' e' → g w' e')
          → Σ∈𝔹 B f → Σ∈𝔹 B g
Σ∈𝔹Func {B} isect {w} {f} {g} (b1 , i1) (b2 , i2) =
  ∩𝔹 isect b1 b2 , i
  where
    i : ∈𝔹 (∩𝔹 isect b1 b2) g
    i e (w₁ , w₂ , b₁ , b₂ , e₁ , e₂) w' e' z =
      i1 (𝔹.ext b1 b₁) b₁ w' (⊑-trans· e₁ e') z
         (i2 (𝔹.ext b2 b₂) b₂ w' (⊑-trans· e₂ e') z)


∀𝕎-Σ∈𝔹Func : {B : Bars} {w : 𝕎·} {f g : wPred w}
              → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
              → Σ∈𝔹 B f → Σ∈𝔹 B g
∀𝕎-Σ∈𝔹Func {B} {w} {f} {g} aw (b , i) = b , j
  where
    j : ∈𝔹 b g
    j e b' w' e' z = aw w' z (i (𝔹.ext b b') b' w' e' z)


∀𝕎-Σ∈𝔹 : {B : Bars} (all : Bars∀ B) {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → Σ∈𝔹 B f
∀𝕎-Σ∈𝔹 {B} all {w} {f} h = 𝔹∀ all w , i
  where
    i : ∈𝔹 {B} (𝔹∀ all w) f
    i {w'} e b w1 e1 z = h w1 z


Σ∈𝔹-Σ∈𝔹' : {B : Bars} (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} {g : wPredDep f}
             → Σ∈𝔹 B (λ w' e' → (x : f w' e') → g w' e' x)
             → (i : Σ∈𝔹 B f) → Σ∈𝔹' B i g
Σ∈𝔹-Σ∈𝔹' {B} mon {w} {f} {g} (b1 , i1) (b2 , i2) {w'} e ib =
  𝔹⊑ mon e b1 , j
  where
    j : ∈𝔹Dep (𝔹⊑ mon e b1) (i2 e ib) (↑wPredDep'' g e)
    j {w0} e0 (w0' , b0 , e0' , e0'') w1 e1 x x' = i1 (𝔹.ext b1 b0) b0 w1 (⊑-trans· e0' e1) x' (i2 e ib w1 x x')


∀𝕎-Σ∈𝔹-Σ∈𝔹' : {B : Bars} (all : Bars∀ B) {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 B f)
                → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : atBethBar i w' e' x)--} → g w' e' x)
                → Σ∈𝔹' B i g
∀𝕎-Σ∈𝔹-Σ∈𝔹' {B} all {w} {f} {g} (b , i) aw {w'} e ib =
  𝔹∀ all w' , j
  where
    j : ∈𝔹Dep {B} (𝔹∀ all w') (i e ib) (↑wPredDep'' g e)
    j {w0} e0 ib' w1 e1 x y = aw w1 y (i e ib w1 x y)



bar-𝔹⊑→ : {B : Bars} (mon : Bars⊑ B) {w w' : 𝕎·} (e : w ⊑· w') {b : 𝔹 B w} {w0 : 𝕎·}
            → 𝔹.bar (𝔹⊑ mon e b) w0
            → 𝔹.bar b w0
bar-𝔹⊑→ {B} mon {w} {w'} e {b} {w0} h = 𝔹.mon b (fst (snd (snd h))) (fst (snd h))



Σ∈𝔹'-comb-change : {B : Bars} (mon : Bars⊑ B) (isect : Bars∩ B) (fam : BarsFam2 B)
                    {w : 𝕎·} {f₁ f₂ f₃ : wPred w}
                    {g₁ : wPredDep f₁} {g₂ : wPredDep f₂} {g₃ : wPredDep f₃}
                    (i₁ : Σ∈𝔹 B f₁) (i₂ : Σ∈𝔹 B f₂) (i₃ : Σ∈𝔹 B f₃)
                    → ∀𝕎 w (λ w' e' → (x₁ : f₁ w' e') (x₂ : f₂ w' e') (x₃ : f₃ w' e')
                                     → g₁ w' e' x₁ → g₂ w' e' x₂ → g₃ w' e' x₃)
                    → Σ∈𝔹' B i₁ g₁ → Σ∈𝔹' B i₂ g₂ → Σ∈𝔹' B i₃ g₃
Σ∈𝔹'-comb-change {B} mon isect fam {w} {f₁} {f₂} {f₃} {g₁} {g₂} {g₃} (b₁ , i₁) (b₂ , i₂) (b₃ , i₃) aw z₁ z₂ {w'} e ib =
  ∩𝔹 isect b1 b2 , j
  where
    z₁' : {w0 : 𝕎·} (e0 : w' ⊑· w0) (ib0 : 𝔹.bar (𝔹⊑ mon e b₁) w0)
          → Σ (𝔹 B w0) (λ b' → ∈𝔹Dep {B} b' (i₁ (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₁} ib0)) (↑wPredDep'' g₁ (⊑-trans· e e0)))
    z₁' {w0} e0 (wa , ba , ea₁ , ea₂) = z₁ (⊑-trans· e e0) (𝔹.mon b₁ ea₁ ba)

    b1 : 𝔹 B w'
    b1 = 𝔹fam2 fam (𝔹⊑ mon e b₁)
                (λ {w0} e0 ib0 b' → ∈𝔹Dep {B} b' (i₁ (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₁} ib0))
                                                  (↑wPredDep'' g₁ (⊑-trans· e e0)))
                z₁'

    z₂' : {w0 : 𝕎·} (e0 : w' ⊑· w0) (ib0 : 𝔹.bar (𝔹⊑ mon e b₂) w0)
          → Σ (𝔹 B w0) (λ b' → ∈𝔹Dep {B} b' (i₂ (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₂} ib0)) (↑wPredDep'' g₂ (⊑-trans· e e0)))
    z₂' {w0} e0 (wa , ba , ea₁ , ea₂) = z₂ (⊑-trans· e e0) (𝔹.mon b₂ ea₁ ba)

    b2 : 𝔹 B w'
    b2 = 𝔹fam2 fam (𝔹⊑ mon e b₂)
                (λ {w0} e0 ib0 b' → ∈𝔹Dep {B} b' (i₂ (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₂} ib0))
                                                  (↑wPredDep'' g₂ (⊑-trans· e e0)))
                z₂'

    j : ∈𝔹Dep (∩𝔹 isect b1 b2) (i₃ e ib) (↑wPredDep'' g₃ e)
    j {w2} e2 (wx , wy , (mk𝔹In wx1 ex1 (wx2 , brx , ex2 , ex3) , bfx) , (mk𝔹In wy1 ey1 (wy2 , bry , ey2 , ey3) , bfy) , ex , ey) w3 e3 x x₁ =
      aw w3 x₁
         (i₁ (⊑-trans· e ex1) (𝔹.mon b₁ ex2 brx) w3 (⊑-trans· (𝔹.ext (fst (z₁' ex1 (wx2 , brx , ex2 , ex3))) bfx) (⊑-trans· ex e3)) x₁)
         (i₂ (⊑-trans· e ey1) (𝔹.mon b₂ ey2 bry) w3 (⊑-trans· (𝔹.ext (fst (z₂' ey1 (wy2 , bry , ey2 , ey3))) bfy) (⊑-trans· ey e3)) x₁)
         (i₃ e ib w3 x x₁)
         (snd (z₁' ex1 (wx2 , brx , ex2 , ex3)) (𝔹.ext (fst (z₁' ex1 (wx2 , brx , ex2 , ex3))) bfx) bfx w3 (⊑-trans· ex e3) (⊑-trans· (𝔹.ext (fst (z₁' ex1 (wx2 , brx , ex2 , ex3))) bfx) (⊑-trans· ex e3)) x₁)
         (snd (z₂' ey1 (wy2 , bry , ey2 , ey3)) (𝔹.ext (fst (z₂' ey1 (wy2 , bry , ey2 , ey3))) bfy) bfy w3 (⊑-trans· ey e3) (⊑-trans· (𝔹.ext (fst (z₂' ey1 (wy2 , bry , ey2 , ey3))) bfy) (⊑-trans· ey e3)) x₁)




{--
old-Σ∈𝔹-idem : {B : Bars} (fam : BarsFam1 B) {w : 𝕎·} {f : wPred w}
            → Σ∈𝔹 B (λ w' e' → Σ∈𝔹 B (↑wPred' f e'))
            → Σ∈𝔹 B f
old-Σ∈𝔹-idem {B} fam {w} {f} (b , i) =
  𝔹fam fam {w} b (λ w1 e1 z b' → ∈𝔹 {B} b' (↑wPred' f z)) i , j
  where
    j : ∈𝔹 {B} (𝔹fam fam {w} b (λ w1 e1 z b' → ∈𝔹 {B} b' (↑wPred' f z)) i) f
    j {w'} e (mk𝔹Fam w2 e2 br₁ w3 e3 z₁ , br) w1 e1 z =
      snd (i e2 br₁ w3 e3 z₁)
          (𝔹.ext (proj₁ (i e2 br₁ w3 e3 z₁)) br)
          br w1 e1 (⊑-trans· (𝔹.ext (proj₁ (i e2 br₁ w3 e3 z₁)) br) e1) z
--}


Σ∈𝔹-idem : {B : Bars} (fam : BarsFam2 B) {w : 𝕎·} {f : wPred w}
            → Σ∈𝔹 B (λ w' e' → Σ∈𝔹 B (↑wPred' f e'))
            → Σ∈𝔹 B f
Σ∈𝔹-idem {B} fam {w} {f} (b , i) =
  𝔹fam2 fam {w} b (λ {w'} e ib bw → ∈𝔹 {B} bw (↑wPred' f e)) (λ {w'} e ib → i e ib w' (⊑-refl· _) e) , j
  where
    j : ∈𝔹 (𝔹fam2 fam b (λ {w'} e ib bw → ∈𝔹 bw (↑wPred' f e)) (λ {w'} e ib → i e ib w' (⊑-refl· w') e)) f
    j {w'} e (mk𝔹In w2 e2 br₁ , br) w1 e1 z =
      snd (i e2 br₁ w2 (⊑-refl· _) e2)
          (𝔹.ext (proj₁ (i e2 br₁ w2 (⊑-refl· _) e2)) br)
          br w1 e1
          (⊑-trans· (𝔹.ext (proj₁ (i e2 br₁ w2 (⊑-refl· _) e2)) br) e1)
          z


{--
old-Σ∈𝔹'-idem : {B : Bars} (mon : Bars⊑ B) (fam : BarsFam1 B)
             {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 B f)
             → Σ∈𝔹 B (λ w' e' → Σ∈𝔹' B (↑'Σ∈𝔹 mon i e') (↑wPredDep' g e'))
             → Σ∈𝔹' B i g
old-Σ∈𝔹'-idem {B} mon fam {w} {f} {g} (b₁ , i) (b₂ , j) {w'} e ib =
  𝔹fam fam {w'} (𝔹⊑ mon e b₂) (λ {w0} e0 {w1} e1 z b' → ∈𝔹Dep {B} b'
                                                                  (λ w2 e2 z' y' → i e ib _ (⊑-trans· z e2) y')
                                                                  (↑wPredDep'' (↑wPredDep' g (⊑-trans· e e0)) e1)) j' ,
  jd
  where
    j' : {w0 : 𝕎·} (e0 : w' ⊑· w0) (ib0 : 𝔹.bar (𝔹⊑ mon e b₂) w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w' ⊑· w1)
         → Σ (𝔹 B w1) (λ b' → ∈𝔹Dep {B} b' (λ w2 e2 z' y' → i e ib _ (⊑-trans· z e2) y') (↑wPredDep'' (↑wPredDep' g (⊑-trans· e e0)) e1))
    j' {w0} e0 (wa , ba , ea₁ , ea₂) w1 e1 z =
      j (𝔹.ext b₂ ba) ba w0 ea₁ (⊑-trans· e e0) e1 (w' , ib , ⊑-trans· e0 e1 , e1)

    jd : ∈𝔹Dep {B} (𝔹fam fam (𝔹⊑ mon e b₂) (λ {w0} e0 {w1} e1 z b' → ∈𝔹Dep {B} b' (λ w2 e2 z' y' → i e ib _ (⊑-trans· z e2) y') (↑wPredDep'' (↑wPredDep' g (⊑-trans· e e0)) e1)) j')
                    (i e ib)
                    (↑wPredDep'' g e)
    jd {w0} e0 (mk𝔹Fam w2 e2 br w3 e3 z , b0) w1 e1 x y =
      snd (j' e2 br w3 e3 z)
          (𝔹.ext (proj₁ (j' e2 br w3 e3 z)) b0)
          b0 w1 e1
          (⊑-trans· (𝔹.ext (proj₁ (j' e2 br w3 e3 z)) b0) e1)
          (⊑-trans· e3 (⊑-trans· (𝔹.ext (proj₁ (j' e2 br w3 e3 z)) b0) e1))
          y
          (i e ib w1 x y)
--}


Σ∈𝔹'-idem : {B : Bars} (mon : Bars⊑ B) (fam : BarsFam2 B)
             {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 B f)
             → Σ∈𝔹 B (λ w' e' → Σ∈𝔹' B (↑'Σ∈𝔹 mon i e') (↑wPredDep' g e'))
             → Σ∈𝔹' B i g
Σ∈𝔹'-idem {B} mon fam {w} {f} {g} (b₁ , i) (b₂ , j) {w'} e ib =
  𝔹fam2 fam {w'} (𝔹⊑ mon e b₂)
         (λ {w₁} e₁ (wa , ba , ea₁ , ea₂) b' → ∈𝔹Dep {B} b' (λ w2 e2 z' y' → i e ib _ (⊑-trans· ea₂ e2) y') (↑wPredDep'' (↑wPredDep' g (⊑-trans· e ea₂)) (⊑-refl· _)))
         (λ {w₁} e₁ (wa , ba , ea₁ , ea₂) → j (𝔹.ext b₂ ba) ba w₁ ea₁ (⊑-trans· e ea₂) (⊑-refl· _) (w' , ib , ea₂ , ⊑-refl· _)) ,
  jd
  where
    jd : ∈𝔹Dep (𝔹fam2 fam (𝔹⊑ mon e b₂)
                        (λ {w₁} e₁ (wa , ba , ea₁ , ea₂) b' → ∈𝔹Dep b' (λ w2 e2 z' y' → i e ib w2 (⊑-trans· ea₂ e2) y') (↑wPredDep'' (↑wPredDep' g (⊑-trans· e ea₂)) (⊑-refl· _)))
                        (λ {w₁} e₁ (wa , ba , ea₁ , ea₂) → j (𝔹.ext b₂ ba) ba w₁ ea₁ (⊑-trans· e ea₂) (⊑-refl· _) (w' , ib , ea₂ , ⊑-refl· _)))
                (i e ib)
                (↑wPredDep'' g e)
    jd {w0} eo (mk𝔹In w2 e2 (wa , ba , ea₁ , ea₂) , b0) w1 e1 x y =
      snd (j (𝔹.ext b₂ ba) ba w2 ea₁ (⊑-trans· e ea₂) (⊑-refl· w2) (w' , ib , ea₂ , ⊑-refl· w2))
          (𝔹.ext (fst (j (𝔹.ext b₂ ba) ba w2 ea₁ (⊑-trans· e ea₂) (⊑-refl· w2) (w' , ib , ea₂ , ⊑-refl· w2))) b0)
          b0
          w1
          e1
          (⊑-trans· (𝔹.ext (fst (j (𝔹.ext b₂ ba) ba w2 ea₁ (⊑-trans· e ea₂) (⊑-refl· w2) (w' , ib , ea₂ , ⊑-refl· w2))) b0) e1)
          (⊑-trans· (𝔹.ext (fst (j (𝔹.ext b₂ ba) ba w2 ea₁ (⊑-trans· e ea₂) (⊑-refl· w2) (w' , ib , ea₂ , ⊑-refl· w2))) b0) e1)
          y
          (i e ib w1 x y)



∀𝕎-Σ∈𝔹'-Σ∈𝔹 : {B : Bars} (fam : BarsFam2 B)
                 {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : Σ∈𝔹 B f)
                 → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                 → Σ∈𝔹' B i g → Σ∈𝔹 B h
∀𝕎-Σ∈𝔹'-Σ∈𝔹 {B} fam {w} {f} {g} {h} (b , i) aw j =
  𝔹fam2 fam {w} b (λ {w'} e ib b' → ∈𝔹Dep {B} b' (i e ib) (↑wPredDep'' g e)) j , i'
  where
    i' : ∈𝔹 {B} (𝔹fam2 fam {w} b (λ {w'} e ib b' → ∈𝔹Dep {B} b' (i e ib) (↑wPredDep'' g e)) j) h
    i' {w'} e (mk𝔹In w2 e2 br , F) w1 e1 z =
      aw w1 z
         (i e2 br w1 (⊑-trans· (𝔹.ext (proj₁ (j e2 br)) F) e1) z)
         (snd (j e2 br)
              (𝔹.ext (proj₁ (j e2 br)) F)
              F w1 e1
              (⊑-trans· (𝔹.ext (proj₁ (j e2 br)) F) e1)
              z)



-- This really only need isect, but can conveniently be derived from Σ∈𝔹'-comb-change
Σ∈𝔹'-comb : {B : Bars} (mon : Bars⊑ B) (isect : Bars∩ B) (fam : BarsFam2 B)
             {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : Σ∈𝔹 B f)
             → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                              → g w' e' zg → h w' e' zh → k w' e' z)
             → Σ∈𝔹' B i g → Σ∈𝔹' B i h → Σ∈𝔹' B i k
Σ∈𝔹'-comb {B} mon isect fam {w} {f} {g} {h} {k} i aw j₁ j₂ =
  Σ∈𝔹'-comb-change {B} mon isect fam {w} {f} {f} {f} {g} {h} {k}
                    i i i (λ w1 e1 x₁ x₂ x₃ a b → aw w1 e1 x₃ x₁ x₂ a b) j₁ j₂

{--
Σ∈𝔹'-comb : {B : Bars} (mon : Bars⊑ B) (isect : Bars∩ B) (fam : BarsFam2 B)
             {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : Σ∈𝔹 B f)
             → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                              → g w' e' zg → h w' e' zh → k w' e' z)
             → Σ∈𝔹' B i g → Σ∈𝔹' B i h → Σ∈𝔹' B i k
Σ∈𝔹'-comb {B} mon isect fam {w} {f} {g} {h} {k} (b , i) aw j₁ j₂ {w'} e ib =
  ∩𝔹 isect b1 b2 , j
  where
    b1 : 𝔹 B w'
    b1 = fst (j₁ e ib)

    i1 : ∈𝔹Dep {B} b1 (i e ib) (↑wPredDep'' g e)
    i1 = snd (j₁ e ib)

    b2 : 𝔹 B w'
    b2 = fst (j₂ e ib)

    i2 : ∈𝔹Dep {B} b2 (i e ib) (↑wPredDep'' h e)
    i2 = snd (j₂ e ib)

    j : ∈𝔹Dep {B} (∩𝔹 isect b1 b2) (i e ib) (↑wPredDep'' k e)
    j {w0} e0 (wa , wb , ba , bb , ea , eb) w1 e1 x y =
      aw w1 y (i e ib w1 x y) (i e ib w1 x y) (i e ib w1 x y)
         (i1 (𝔹.ext b1 ba) ba w1 (⊑-trans· ea e1) x y)
         (i2 (𝔹.ext b2 bb) bb w1 (⊑-trans· eb e1) x y)
--}


-- This really only needs mon and fam, but can conveniently be derived from Σ∈𝔹'-comb-change
Σ∈𝔹'-change : {B : Bars} (mon : Bars⊑ B) (isect : Bars∩ B) (fam : BarsFam2 B)
               {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k}
               (i : Σ∈𝔹 B f) (j : Σ∈𝔹 B k)
               → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e')
                                → g w' e' x → h w' e' y)
               → Σ∈𝔹' B i g → Σ∈𝔹' B j h
Σ∈𝔹'-change {B} mon isect fam {w} {f} {k} {g} {h} i j aw z =
  Σ∈𝔹'-comb-change mon isect fam {w} {f} {f} {k} {g} {g} {h} i i j (λ w1 e1 x₁ x₂ x₃ a b → aw w1 e1 x₁ x₃ a) z z

{--
Σ∈𝔹'-change : {B : Bars} (mon : Bars⊑ B) (fam : BarsFam2 B)
               {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k}
               (i : Σ∈𝔹 B f) (j : Σ∈𝔹 B k)
               → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e')
                                → g w' e' x → h w' e' y)
               → Σ∈𝔹' B i g → Σ∈𝔹' B j h
Σ∈𝔹'-change {B} mon fam {w} {f} {k} {g} {h} (b₁ , i) (b₂ , j) aw z {w'} e ib =
  𝔹fam2 fam (𝔹⊑ mon e b₁)
             (λ {w0} e0 ib0 b' → ∈𝔹Dep {B} b' (i (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₁} ib0))
                                               (↑wPredDep'' g (⊑-trans· e e0)))
             z' {--z'--} ,
  jd
  where
    z' : {w0 : 𝕎·} (e0 : w' ⊑· w0) (ib0 : 𝔹.bar (𝔹⊑ mon e b₁) w0)
          → Σ (𝔹 B w0) (λ b' → ∈𝔹Dep {B} b' (i (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₁} ib0)) (↑wPredDep'' g (⊑-trans· e e0)))
    z' {w0} e0 (wa , ba , ea₁ , ea₂) = z (⊑-trans· e e0) (𝔹.mon b₁ ea₁ ba)

    jd : ∈𝔹Dep {B} (𝔹fam2 fam (𝔹⊑ mon e b₁) (λ {w0} e0 ib0 b' → ∈𝔹Dep {B} b' (i (⊑-trans· e e0) (bar-𝔹⊑→ mon e {b₁} ib0)) (↑wPredDep'' g (⊑-trans· e e0))) z')
                    (j e ib)
                    (↑wPredDep'' h e)
    jd {w0} e0 (mk𝔹In w2 e2 (w3 , br , e3 , e4) , b0) w1 e1 x y =
      aw w1 y
         (i (⊑-trans· e e2) (𝔹.mon b₁ e3 br) w1 (⊑-trans· (𝔹.ext (fst (z' e2 (w3 , br , e3 , e4))) b0) e1) y)
         (j e ib w1 x y)
         (snd (z' e2 (w3 , br , e3 , e4))
              (𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0)
              b0 w1 e1
              (⊑-trans· (𝔹.ext (proj₁ (z' e2 (w3 , br , e3 , e4))) b0) e1)
              y)
--}




Σ∈𝔹-const : {B : Bars} (ex : Bars∃ B) {w : 𝕎·} {t : Set(lsuc(L))} → Σ∈𝔹 B {w} (λ w e → t) → t
Σ∈𝔹-const {B} ex {w} {t} (b , i) =
  i (fst (snd (ex (𝔹.bars b) (𝔹.ext b))))
    (snd (snd (ex (𝔹.bars b) (𝔹.ext b))))
    (fst (ex (𝔹.bars b) (𝔹.ext b)))
    (⊑-refl· _)
    (fst (snd (ex (𝔹.bars b) (𝔹.ext b))))


Σ∈𝔹→∃ : {B : Bars} (ex : Bars∃ B) {w : 𝕎·} {f : wPred w} → Σ∈𝔹 B {w} f → ∃𝕎 w λ w' e → f w' e
Σ∈𝔹→∃ {B} ex {w} {f} (b , i) =
  fst (ex (𝔹.bars b) (𝔹.ext b)) ,
  fst (snd (ex (𝔹.bars b) (𝔹.ext b))) ,
  i (𝔹.ext b (snd (snd (ex (𝔹.bars b) (𝔹.ext b)))))
    (snd (snd (ex (𝔹.bars b) (𝔹.ext b))))
    (fst (ex (𝔹.bars b) (𝔹.ext b)))
    (⊑-refl· _)
    (fst (snd (ex (𝔹.bars b) (𝔹.ext b))))



-- TODO: is this derivable from the others?
→Σ∈𝔹∀𝕎 : {B : Bars} {w : 𝕎·} {f : wPred w}
            → Σ∈𝔹 B f
            → Σ∈𝔹 B (λ w' e → ∀𝕎 w' (↑wPred f e))
→Σ∈𝔹∀𝕎 {B} {w} {f} (b , i) = b , j
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
record BarsProps : Set(lsuc(lsuc(L))) where
  constructor mkBarsProps
  field
    bars  : Bars
    mon   : Bars⊑ bars
    isect : Bars∩ bars
    all   : Bars∀ bars    -- top element
    fam2  : BarsFam2 bars -- arbitrary unions
    ex    : Bars∃ bars    -- bars are non-empty
--    fam1  : BarsFam1 bars
\end{code}
