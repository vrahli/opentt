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
open import choice
open import getChoice
open import newChoice
open import freeze
open import progress


-- TODO: move the instances to separate files.
-- Choice is only needed for Beth bars to build an infinite sequence of worlds
module bar {L : Level} (W : PossibleWorlds {L})
           (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
       where
open import worldDef{L}(W)

-- Those are only needed by the Beth instance
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
open import progressDef(W)(C)(G)(N)(F)(P)




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


Σ∈𝔹 : {B : Bars} (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
Σ∈𝔹 {B} w f = Σ (𝔹 B w) (λ b → ∈𝔹 b f)


∈𝔹Dep : {B : Bars} {w : 𝕎·} (b : 𝔹 B w) {g : wPred w} (i : ∀𝕎 w g) (f : wPredDep g) → Set(lsuc(L))
∈𝔹Dep {B} {w} b {g} i f =
  {w' : 𝕎·} (e : w ⊑· w') → 𝔹.bar b w'
  → ∀𝕎 w' (λ w'' e' → (x : w ⊑· w'') → f w'' x (i w'' x))


Σ∈𝔹' : {B : Bars} (w : 𝕎·) {g : wPred w} (h : Σ∈𝔹 {B} w g) (f : wPredDep g) → Set(lsuc(L))
Σ∈𝔹' {B} w {g} (b , i) f =
  {w1 : 𝕎·} (e1 : w ⊑· w1) (ib : 𝔹.bar b w1)
  → Σ (𝔹 B w1) (λ b' → ∈𝔹Dep b' (i e1 ib) (↑wPredDep'' f e1))


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


{-- Intersection --}
bar∩ : 𝕎· → Br → Br → Br
bar∩ w b1 b2 w0 = Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → b1 w1 × b2 w2 × w1 ⊑· w0 × w2 ⊑· w0))


Bars∩ : (B : Bars) → Set(lsuc(L))
Bars∩ B =
  {w : 𝕎·} (b1 b2 : Br)
  → B w b1
  → B w b2
  → B w (bar∩ w b1 b2)


∩𝔹 : {B : Bars} (isect : Bars∩ B) {w : 𝕎·} → 𝔹 B w → 𝔹 B w → 𝔹 B w
∩𝔹 {B} isect {w} (mk𝔹 b1 bars1 ext1 mon1) (mk𝔹 b2 bars2 ext2 mon2) =
  mk𝔹 bar bars ext mon
  where
    bar : Br
    bar = bar∩ w b1 b2

    bars : B w bar
    bars = isect b1 b2 bars1 bars2

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (w1 , w2 , b₁ , b₂ , e₁ , e₂) = ⊑-trans· (𝔹.ext {B} {w} (mk𝔹 b1 bars1 ext1 mon1) {w1} b₁) e₁

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (wa , wb , ba , bb , ea , eb) = wa , wb , ba , bb , ⊑-trans· ea e , ⊑-trans· eb e



{-- Triviality? --}
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


{-- Families(2) --}
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

↑Σ∈𝔹 : {B : Bars} (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} (i : Σ∈𝔹 {B} w f) {w' : 𝕎·} (e : w ⊑· w') → Σ∈𝔹 {B} w' (↑wPred f e)
↑Σ∈𝔹 {B} mon {w} {f} (b , i) {w'} e = 𝔹⊑ mon e b , j
  where
    j : ∈𝔹 (𝔹⊑ mon e b) (↑wPred f e)
    j {w1} e1 (w0 , b0 , e₁ , e₂) w2 e2 z = i (𝔹.ext b {w0} b0) b0 w2 (⊑-trans· e₁ e2) (⊑-trans· e z)


↑'Σ∈𝔹 : {B : Bars} (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} (i : Σ∈𝔹 {B} w f) {w' : 𝕎·} (e : w ⊑· w') → Σ∈𝔹 {B} w' (↑wPred' f e)
↑'Σ∈𝔹 {B} mon {w} {f} (b , i) {w'} e = 𝔹⊑ mon e b , j
  where
    j : ∈𝔹 (𝔹⊑ mon e b) (↑wPred' f e)
    j {w1} e1 (w0 , b0 , e₁ , e₂) w2 e2 z x = i (𝔹.ext b {w0} b0) b0 w2 (⊑-trans· e₁ e2) x




↑Σ∈𝔹' : {B : Bars}  (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 {B} w f) {w' : 𝕎·} (e : w ⊑· w')
         → Σ∈𝔹' {B} w i g → Σ∈𝔹' {B} w' (↑Σ∈𝔹 mon i e) (↑wPredDep g e)
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
          → Σ∈𝔹 {B} w (λ w' e' → f w' e' → g w' e')
          → Σ∈𝔹 {B} w f → Σ∈𝔹 {B} w g
Σ∈𝔹Func {B} isect {w} {f} {g} (b1 , i1) (b2 , i2) =
  ∩𝔹 isect b1 b2 , i
  where
    i : ∈𝔹 (∩𝔹 isect b1 b2) g
    i e (w₁ , w₂ , b₁ , b₂ , e₁ , e₂) w' e' z =
      i1 (𝔹.ext b1 b₁) b₁ w' (⊑-trans· e₁ e') z
         (i2 (𝔹.ext b2 b₂) b₂ w' (⊑-trans· e₂ e') z)


∀𝕎-Σ∈𝔹Func : {B : Bars} {w : 𝕎·} {f g : wPred w}
              → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
              → Σ∈𝔹 {B} w f → Σ∈𝔹 {B} w g
∀𝕎-Σ∈𝔹Func {B} {w} {f} {g} aw (b , i) = b , j
  where
    j : ∈𝔹 b g
    j e b' w' e' z = aw w' z (i (𝔹.ext b b') b' w' e' z)


∀𝕎-Σ∈𝔹 : {B : Bars} (all : Bars∀ B) {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → Σ∈𝔹 {B} w f
∀𝕎-Σ∈𝔹 {B} all {w} {f} h = 𝔹∀ all w , i
  where
    i : ∈𝔹 {B} (𝔹∀ all w) f
    i {w'} e b w1 e1 z = h w1 z


Σ∈𝔹-Σ∈𝔹' : {B : Bars} (mon : Bars⊑ B) {w : 𝕎·} {f : wPred w} {g : wPredDep f}
             → Σ∈𝔹 {B} w (λ w' e' → (x : f w' e') → g w' e' x)
             → (i : Σ∈𝔹 {B} w f) → Σ∈𝔹' {B} w i g
Σ∈𝔹-Σ∈𝔹' {B} mon {w} {f} {g} (b1 , i1) (b2 , i2) {w'} e ib =
  𝔹⊑ mon e b1 , j
  where
    j : ∈𝔹Dep (𝔹⊑ mon e b1) (i2 e ib) (↑wPredDep'' g e)
    j {w0} e0 (w0' , b0 , e0' , e0'') w1 e1 x x' = i1 (𝔹.ext b1 b0) b0 w1 (⊑-trans· e0' e1) x' (i2 e ib w1 x x')


∀𝕎-Σ∈𝔹-Σ∈𝔹' : {B : Bars} (all : Bars∀ B) {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 {B} w f)
                → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : atBethBar i w' e' x)--} → g w' e' x)
                → Σ∈𝔹' {B} w i g
∀𝕎-Σ∈𝔹-Σ∈𝔹' {B} all {w} {f} {g} (b , i) aw {w'} e ib =
  𝔹∀ all w' , j
  where
    j : ∈𝔹Dep {B} (𝔹∀ all w') (i e ib) (↑wPredDep'' g e)
    j {w0} e0 ib' w1 e1 x y = aw w1 y (i e ib w1 x y)



Σ∈𝔹'-comb : {B : Bars} (isect : Bars∩ B) {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : Σ∈𝔹 {B} w f)
             → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                              → g w' e' zg → h w' e' zh → k w' e' z)
             → Σ∈𝔹' {B} w i g → Σ∈𝔹' {B} w i h → Σ∈𝔹' {B} w i k
Σ∈𝔹'-comb {B} isect {w} {f} {g} {h} {k} (b , i) aw j₁ j₂ {w'} e ib =
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



Σ∈𝔹-idem : {B : Bars} (fam : BarsFam1 B) {w : 𝕎·} {f : wPred w}
            → Σ∈𝔹 {B} w (λ w' e' → Σ∈𝔹 {B} w' (↑wPred' f e'))
            → Σ∈𝔹 {B} w f
Σ∈𝔹-idem {B} fam {w} {f} (b , i) =
  𝔹fam fam {w} b (λ w1 e1 z b' → ∈𝔹 {B} b' (↑wPred' f z)) i , j
  where
    j : ∈𝔹 {B} (𝔹fam fam {w} b (λ w1 e1 z b' → ∈𝔹 {B} b' (↑wPred' f z)) i) f
    j {w'} e (mk𝔹Fam w2 e2 br₁ w3 e3 z₁ , br) w1 e1 z =
      snd (i e2 br₁ w3 e3 z₁)
          (𝔹.ext (proj₁ (i e2 br₁ w3 e3 z₁)) br)
          br w1 e1 (⊑-trans· (𝔹.ext (proj₁ (i e2 br₁ w3 e3 z₁)) br) e1) z



Σ∈𝔹'-idem : {B : Bars} (mon : Bars⊑ B) (fam : BarsFam1 B)
             {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : Σ∈𝔹 {B} w f)
             → Σ∈𝔹 {B} w (λ w' e' → Σ∈𝔹' {B} w' (↑'Σ∈𝔹 mon i e') (↑wPredDep' g e'))
             → Σ∈𝔹' {B} w i g
Σ∈𝔹'-idem {B} mon fam {w} {f} {g} (b₁ , i) (b₂ , j) {w'} e ib =
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


bar-𝔹⊑→ : {B : Bars} (mon : Bars⊑ B) {w w' : 𝕎·} (e : w ⊑· w') {b : 𝔹 B w} {w0 : 𝕎·}
            → 𝔹.bar (𝔹⊑ mon e b) w0
            → 𝔹.bar b w0
bar-𝔹⊑→ {B} mon {w} {w'} e {b} {w0} h = 𝔹.mon b (fst (snd (snd h))) (fst (snd h))



∀𝕎-Σ∈𝔹'-Σ∈𝔹 : {B : Bars} (fam : BarsFam2 B)
                 {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : Σ∈𝔹 {B} w f)
                 → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                 → Σ∈𝔹' {B} w i g → Σ∈𝔹 {B} w h
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



Σ∈𝔹'-change : {B : Bars} (mon : Bars⊑ B) (fam : BarsFam2 B)
               {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k}
               (i : Σ∈𝔹 {B} w f) (j : Σ∈𝔹 {B} w k)
               → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e')
                                → g w' e' x → h w' e' y)
               → Σ∈𝔹' {B} w i g → Σ∈𝔹' {B} w j h
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


Σ∈𝔹-const : {B : Bars} (ex : Bars∃ B) {w : 𝕎·} {t : Set(lsuc(L))} → Σ∈𝔹 {B} w (λ w e → t) → t
Σ∈𝔹-const {B} ex {w} {t} (b , i) =
  i (fst (snd (ex (𝔹.bars b) (𝔹.ext b))))
    (snd (snd (ex (𝔹.bars b) (𝔹.ext b))))
    (fst (ex (𝔹.bars b) (𝔹.ext b)))
    (⊑-refl· _)
    (fst (snd (ex (𝔹.bars b) (𝔹.ext b))))


{-- Those are all the properties we need about Bars to derive the above properties,
    which in turn are the properties of Bar below.
    We show 2 intances below:
    (1) O𝔹BarsProps for open bars
    (2) IS𝔹BarsProps for Beth Bars
 --}
record BarsProps : Set(lsuc(lsuc(L))) where
  constructor mkBarsProps
  field
    bars  : Bars
    mon   : Bars⊑ bars
    isect : Bars∩ bars
    all   : Bars∀ bars
    fam1  : BarsFam1 bars
    fam2  : BarsFam2 bars
    ex    : Bars∃ bars



record Bar : Set(lsuc(lsuc(L))) where
  constructor mkBar
  field
    -- ## Operators
    inBar             : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
    inBar'            : (w : 𝕎·) {g : wPred w} (h : inBar w g) (f : wPredDep g) → Set(lsuc(L))

    -- ## Axioms
    -- Monotonicity of the operators
    ↑inBar            : {w : 𝕎·} {f : wPred w} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBar w' (↑wPred f e)
    ↑'inBar           : {w : 𝕎·} {f : wPred w} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBar w' (↑wPred' f e)
    ↑inBar'           : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f) {w' : 𝕎·} (e : w ⊑· w')
                        → inBar' w i g → inBar' w' (↑inBar i e) (↑wPredDep g e)

    -- axiom K: □(A→B)→□A→□B
    inBarFunc         : {w : 𝕎·} {f g : wPred w}
                        → inBar w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    -- similar to axiom K??
    ∀𝕎-inBarFunc    : {w : 𝕎·} {f g : wPred w}
                        → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
                        → inBar w f → inBar w g
    -- □ → □'
    inBar-inBar'      : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                        → inBar w (λ w' e' → (x : f w' e') → g w' e' x)
                        → (i : inBar w f) → inBar' w i g
    -- similar to above without □
    ∀𝕎-inBar-inBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : atBar i w' e' x)--} → g w' e' x)
                        → inBar' w i g

    -- name?
    ∀𝕎-inBar        : {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → inBar w f

    -- □□A→□A name?
    inBar-idem        : {w : 𝕎·} {f : wPred w}
                        → inBar w (λ w' e' → inBar w' (↑wPred' f e'))
                        → inBar w f
    -- similar to above
    inBar'-idem       : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBar w f)
                        → inBar w (λ w' e' → inBar' w' (↑'inBar i e') (↑wPredDep' g e'))
                        → inBar' w i g

    -- □' → □
    ∀𝕎-inBar'-inBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inBar w f)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') {--→ atBar i w' e' x--} → g w' e' x → h w' e')
                        → inBar' w i g → inBar w h

    -- (A→B→C) → □'A→□'B→□'C
    inBar'-comb       : {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : inBar w f)
                        → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                                           → g w' e' zg → h w' e' zh → k w' e' z)
                        → inBar' w i g → inBar' w i h → inBar' w i k

    -- (A→B) → □'A→□'B
    inBar'-change    : {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k} (i : inBar w f) (j : inBar w k)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e') {--→ atBar i w' e' x → atBar j w' e' y--}
                                           → g w' e' x → h w' e' y)
                        → inBar' w i g → inBar' w j h

    -- □A→A some version of T?
    inBar-const       : {w : 𝕎·} {t : Set(lsuc(L))} → inBar w (λ w e → t) → t


--    atBar             : {w : 𝕎·} {f : wPred w} (i : inBar w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
--    atBar-refl        : {w : 𝕎·} {f : wPred w} (i : inBar w f) (p : f w (⊑-refl· w)) → atBar {w} {f} i w (⊑-refl· w) p

--    wPredDepExtIrrBar : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : inBar w f) → Set(lsuc(L))
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
inBar'-inBar b {w} {f} {h} i q = Bar.∀𝕎-inBar'-inBar b i (λ w1 e1 x {--at--} z → z) q


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



BarsProps→Bar : BarsProps → Bar
BarsProps→Bar b =
  mkBar
    (Σ∈𝔹 {BarsProps.bars b})
    (Σ∈𝔹' {BarsProps.bars b})
    (↑Σ∈𝔹 (BarsProps.mon b))
    (↑'Σ∈𝔹 (BarsProps.mon b))
    (λ {w} {f} {g} → ↑Σ∈𝔹' (BarsProps.mon b) {w} {f} {g})
    (Σ∈𝔹Func (BarsProps.isect b))
    (∀𝕎-Σ∈𝔹Func {BarsProps.bars b})
    (Σ∈𝔹-Σ∈𝔹' (BarsProps.mon b))
    (∀𝕎-Σ∈𝔹-Σ∈𝔹' (BarsProps.all b))
    (∀𝕎-Σ∈𝔹 (BarsProps.all b))
    (Σ∈𝔹-idem (BarsProps.fam1 b))
    (Σ∈𝔹'-idem (BarsProps.mon b) (BarsProps.fam1 b))
    (∀𝕎-Σ∈𝔹'-Σ∈𝔹 (BarsProps.fam2 b))
    (Σ∈𝔹'-comb (BarsProps.isect b))
    (Σ∈𝔹'-change (BarsProps.mon b) (BarsProps.fam2 b))
    (Σ∈𝔹-const (BarsProps.ex b))



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


O𝔹barsFam1 : BarsFam1 O𝔹bars
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
    O𝔹barsFam1
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


Σ∈𝔹→inOpenBar : (w : 𝕎·) (f : wPred w) → Σ∈𝔹 {O𝔹bars} w f → inOpenBar w f
Σ∈𝔹→inOpenBar w f (b , i) w1 e1 =
  fst (𝔹.bars b w1 e1) ,
  fst (snd (𝔹.bars b w1 e1)) ,
  j
  where
    j : ∀𝕎 (fst (𝔹.bars b w1 e1)) (λ w3 e3 → (z : w ⊑· w3) → f w3 z)
    j w2 e2 z = i (⊑-trans· e1 (fst (snd (𝔹.bars b w1 e1)))) (lower (snd (snd (𝔹.bars b w1 e1)))) w2 e2 z



inOpenBar→Σ∈𝔹 : (w : 𝕎·) (f : wPred w) → inOpenBar w f → Σ∈𝔹 {O𝔹bars} w f
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
Σ∈𝔹'→inOpenBar' : (w : 𝕎·) {g : wPred w} (h : Σ∈𝔹 {O𝔹bars} w g) (f : wPredDep g)
                    → Σ∈𝔹' {O𝔹bars} w {g} h f
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
                    → Σ∈𝔹' {O𝔹bars} w {g} (inOpenBar→Σ∈𝔹 w g h) f
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
    inOpenBar'-comb
    inOpenBar'-change
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



{--


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


--}



{-----------------------------------------
 --
 -- Beth Bar instance -- defined from infinite sequences
 --
 --}
record BarredChain (bar : Br) {w : 𝕎·} (c : chain w) : Set(L) where
  constructor mkBarredChain
  field
    w'  : 𝕎·
    b   : bar w'
    n   : ℕ
    ext : w' ⊑· chain.seq c n


IS𝔹bars : Bars
IS𝔹bars w bar = (c : pchain w) → BarredChain bar (pchain.c c)

-- a Beth bar where all infinite sequences are barred
IS𝔹 : 𝕎· → Set(lsuc(L))
IS𝔹 w = 𝔹 IS𝔹bars w

inBethBar : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
inBethBar = Σ∈𝔹 {IS𝔹bars}

inBethBar' : (w : 𝕎·) {g : wPred w} (h : inBethBar w g) (f : wPredDep g) → Set(lsuc(L))
inBethBar' = Σ∈𝔹' {IS𝔹bars}



-- We prove that Beth bars are monotonic
IS𝔹bars⊑ : Bars⊑ IS𝔹bars
IS𝔹bars⊑ {w1} {w2} e bar h c =
  mkBarredChain
    (chain.seq (chain⊑ e (pchain.c c)) (BarredChain.n z))
    (BarredChain.w' z , BarredChain.b z , BarredChain.ext z , chain⊑n (BarredChain.n z) (pchain.c c))
    (BarredChain.n z)
    (⊑-refl· _)
    where
      z : BarredChain bar (chain⊑ e (pchain.c c))
      z = h (pchain⊑ e c)


IS𝔹bars∩ : Bars∩ IS𝔹bars
IS𝔹bars∩ {w} b1 b2 bars1 bars2 c =
  mkBarredChain (chain.seq (pchain.c c) ((BarredChain.n z1) ⊔ (BarredChain.n z2)))
             (BarredChain.w' z1 , BarredChain.w' z2 , BarredChain.b z1 , BarredChain.b z2 , e1 , e2)
             ((BarredChain.n z1) ⊔ (BarredChain.n z2))
             (⊑-refl· _)
  where
    z1 : BarredChain b1 (pchain.c c) --Σ 𝕎· (λ w' → b1 w' × Σ ℕ (λ n → w' ⊑· chain.seq c n))
    z1 = bars1 c

    z2 : BarredChain b2 (pchain.c c) --Σ 𝕎· (λ w' → b2 w' × Σ ℕ (λ n → w' ⊑· chain.seq c n))
    z2 = bars2 c

    e1 : BarredChain.w' z1 ⊑· chain.seq (pchain.c c) (BarredChain.n z1 ⊔ BarredChain.n z2)
    e1 = ⊑-trans· (BarredChain.ext z1) (≤→chain⊑ (pchain.c c) (m≤m⊔n (BarredChain.n z1) (BarredChain.n z2)))

    e2 : BarredChain.w' z2 ⊑· chain.seq (pchain.c c) (BarredChain.n z1 ⊔ BarredChain.n z2)
    e2 = ⊑-trans· (BarredChain.ext z2) (≤→chain⊑ (pchain.c c) (m≤n⊔m (BarredChain.n z1) (BarredChain.n z2)))


IS𝔹bars∀ : Bars∀ IS𝔹bars
IS𝔹bars∀ w c = mkBarredChain w (⊑-refl· _) 0 (chain.init (pchain.c c))


--IS𝔹Fam : {w : 𝕎·} (b : IS𝔹 w) → Set(L)
--IS𝔹Fam = 𝔹Fam {IS𝔹bars}


IS𝔹barsFam1 : BarsFam1 IS𝔹bars
IS𝔹barsFam1 {w} b G i c =
  mkBarredChain (BarredChain.w' bp') br (BarredChain.n bp' + BarredChain.n bp) e
  where
    bp : BarredChain (𝔹.bar b) (pchain.c c)
    bp = 𝔹.bars b c

    b' : IS𝔹 (BarredChain.w' bp)
    b' = fst (i (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp) (BarredChain.w' bp) (⊑-refl· _) (𝔹.ext b (BarredChain.b bp)))

    bp' : BarredChain (𝔹.bar b') (truncateChain {w} {pchain.c c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))
    bp' = 𝔹.bars b' (truncatePChain {w} {c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))

    br : barFam b G i (BarredChain.w' bp')
    br = mk𝔹Fam (BarredChain.w' bp) (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp) (BarredChain.w' bp) (⊑-refl· _) (𝔹.ext b (BarredChain.b bp)) ,
         BarredChain.b bp'

    e : BarredChain.w' bp' ⊑· chain.seq (pchain.c c) (BarredChain.n bp' + BarredChain.n (𝔹.bars b c))
    e = BarredChain.ext bp'



IS𝔹barsFam2 : BarsFam2 IS𝔹bars
IS𝔹barsFam2 {w} b G i c =
  mkBarredChain (BarredChain.w' bp') br (BarredChain.n bp' + BarredChain.n bp) e
  where
    bp : BarredChain (𝔹.bar b) (pchain.c c)
    bp = 𝔹.bars b c

    b' : IS𝔹 (BarredChain.w' bp)
    b' = fst (i (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp))

    bp' : BarredChain (𝔹.bar b') (truncateChain {w} {pchain.c c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))
    bp' = 𝔹.bars b' (truncatePChain {w} {c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))

    br : barFam2 b G i (BarredChain.w' bp')
    br = mk𝔹In (BarredChain.w' bp) (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp) ,
         BarredChain.b bp'

    e : BarredChain.w' bp' ⊑· chain.seq (pchain.c c) (BarredChain.n bp' + BarredChain.n (𝔹.bars b c))
    e = BarredChain.ext bp'



IS𝔹bars∃ : Bars∃ IS𝔹bars
IS𝔹bars∃ {w} {b} bars ext =
  BarredChain.w' bp , ext (BarredChain.b bp) , BarredChain.b bp
  where
    c : pchain w
    c = 𝕎→pchain w

    bp : BarredChain b (pchain.c c)
    bp = bars c


IS𝔹BarsProps : BarsProps
IS𝔹BarsProps =
  mkBarsProps
    IS𝔹bars
    IS𝔹bars⊑
    IS𝔹bars∩
    IS𝔹bars∀
    IS𝔹barsFam1
    IS𝔹barsFam2
    IS𝔹bars∃




{--
↑inBethBar : {w : 𝕎·} {f : wPred w} (i : inBethBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBethBar w' (↑wPred f e)
↑inBethBar = ↑Σ∈𝔹 {IS𝔹bars} IS𝔹bars⊑


↑'inBethBar : {w : 𝕎·} {f : wPred w} (i : inBethBar w f) {w' : 𝕎·} (e : w ⊑· w') → inBethBar w' (↑wPred' f e)
↑'inBethBar = ↑'Σ∈𝔹 {IS𝔹bars} IS𝔹bars⊑


inBethBarFunc : {w : 𝕎·} {f g : wPred w} → inBethBar w (λ w' e' → f w' e' → g w' e') → inBethBar w f → inBethBar w g
inBethBarFunc = Σ∈𝔹Func {IS𝔹bars} IS𝔹bars∩


∀𝕎-inBethBarFunc : {w : 𝕎·} {f g : wPred w} → ∀𝕎 w (λ w' e' → f w' e' → g w' e') → inBethBar w f → inBethBar w g
∀𝕎-inBethBarFunc = ∀𝕎-Σ∈𝔹Func {IS𝔹bars}


trivialIS𝔹 : (w : 𝕎·) → IS𝔹 w
trivialIS𝔹 = 𝔹∀ {IS𝔹bars} IS𝔹bars∀


∀𝕎-inBethBar : {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → inBethBar w f
∀𝕎-inBethBar = ∀𝕎-Σ∈𝔹 {IS𝔹bars} IS𝔹bars∀


inBethBar-inBethBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                       → inBethBar w (λ w' e' → (x : f w' e') → g w' e' x)
                       → (i : inBethBar w f) → inBethBar' w i g
inBethBar-inBethBar' = Σ∈𝔹-Σ∈𝔹' {IS𝔹bars} IS𝔹bars⊑



∀𝕎-inBethBar-inBethBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBethBar w f)
                           → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : atBethBar i w' e' x)--} → g w' e' x)
                           → inBethBar' w i g
∀𝕎-inBethBar-inBethBar' = ∀𝕎-Σ∈𝔹-Σ∈𝔹' {IS𝔹bars} IS𝔹bars∀


inBethBar'-comb : {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : inBethBar w f)
                  → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                                   → g w' e' zg → h w' e' zh → k w' e' z)
                  → inBethBar' w i g → inBethBar' w i h → inBethBar' w i k
inBethBar'-comb = Σ∈𝔹'-comb {IS𝔹bars} IS𝔹bars∩



↑inBethBar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBethBar w f) {w' : 𝕎·} (e : w ⊑· w')
              → inBethBar' w i g → inBethBar' w' (↑inBethBar i e) (↑wPredDep g e)
↑inBethBar' {w} {F} {g} = ↑Σ∈𝔹' {IS𝔹bars} IS𝔹bars⊑ {w} {F} {g}


inBethBar-idem : {w : 𝕎·} {f : wPred w}
                 → inBethBar w (λ w' e' → inBethBar w' (↑wPred' f e'))
                 → inBethBar w f
inBethBar-idem = Σ∈𝔹-idem {IS𝔹bars} IS𝔹barsFam1


inBethBar'-idem : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inBethBar  w f)
                  → inBethBar w (λ w' e' → inBethBar' w' (↑'inBethBar i e') (↑wPredDep' g e'))
                  → inBethBar' w i g
inBethBar'-idem = Σ∈𝔹'-idem {IS𝔹bars} IS𝔹bars⊑ IS𝔹barsFam1


∀𝕎-inBethBar'-inBethBar : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : inBethBar w f)
                           → ∀𝕎 w (λ w' e' → (x : f w' e') {--→ atBethBar i w' e' x--} → g w' e' x → h w' e')
                           → inBethBar' w i g → inBethBar w h
∀𝕎-inBethBar'-inBethBar = ∀𝕎-Σ∈𝔹'-Σ∈𝔹 {IS𝔹bars} IS𝔹barsFam2


inBethBar'-change : {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k}
                    (i : inBethBar w f) (j : inBethBar w k)
                    → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e') {--→ atBethBar i w' e' x → atBethBar j w' e' y--}
                                     → g w' e' x → h w' e' y)
                    → inBethBar' w i g → inBethBar' w j h
inBethBar'-change = Σ∈𝔹'-change {IS𝔹bars} IS𝔹bars⊑ IS𝔹barsFam2


inBethBar-const : {w : 𝕎·} {t : Set(lsuc(L))} → inBethBar w (λ w e → t) → t
inBethBar-const = Σ∈𝔹-const {IS𝔹bars} IS𝔹bars∃
--}


-- TODO: generate this bar from (BarsProps→Bar IS𝔹BarsProps)
inBethBar-Bar : Bar
inBethBar-Bar = BarsProps→Bar IS𝔹BarsProps
{--  mkBar
    inBethBar
    inBethBar'
    ↑inBethBar
    ↑'inBethBar
    (λ {w} {f} {g} → ↑inBethBar' {w} {f} {g})
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
--}


trivialIS𝔹 : (w : 𝕎·) → IS𝔹 w
trivialIS𝔹 = 𝔹∀ {IS𝔹bars} IS𝔹bars∀

inIS𝔹 : {w : 𝕎·} (b : IS𝔹 w) (f : wPred w) → Set(lsuc(L))
inIS𝔹 = ∈𝔹 {IS𝔹bars}






{--IS𝔹⊑ : {w w' : 𝕎·} (e : w ⊑· w') → IS𝔹 w → IS𝔹 w'
IS𝔹⊑ = 𝔹⊑ {IS𝔹bars} IS𝔹bars⊑--}

{--∩IS𝔹 : {w : 𝕎·} → IS𝔹 w → IS𝔹 w → IS𝔹 w
∩IS𝔹 = ∩𝔹 {IS𝔹bars} IS𝔹bars∩--}

{--inIS𝔹Dep : {w : 𝕎·} (b : IS𝔹 w) {g : wPred w} (i : ∀𝕎 w g) (f : wPredDep g) → Set(lsuc(L))
inIS𝔹Dep = ∈𝔹Dep {IS𝔹bars}--}

{--IS𝔹-fam : {w : 𝕎·} (b : IS𝔹 w)
           (G : {w0 : 𝕎·} (e0 : w ⊑· w0) {w1 : 𝕎·} (e1 : w0 ⊑· w1) (z : w ⊑· w1) → IS𝔹 w1 → Set(lsuc(L)))
           (i : {w0 : 𝕎·} (e0 : w ⊑· w0) (ib0 : 𝔹.bar b w0) (w1 : 𝕎·) (e1 : w0 ⊑· w1) (z : w ⊑· w1)
                → Σ (IS𝔹 w1) (λ b' → G e0 e1 z b'))
           → IS𝔹 w
IS𝔹-fam = 𝔹fam {IS𝔹bars} IS𝔹barsFam
--}

{--bar-IS𝔹⊑→ : {w w' : 𝕎·} (e : w ⊑· w') {b : IS𝔹 w} {w0 : 𝕎·}
              → 𝔹.bar (IS𝔹⊑ e b) w0
              → 𝔹.bar b w0
bar-IS𝔹⊑→ = bar-𝔹⊑→ {IS𝔹bars} IS𝔹bars⊑--}


{--
-- Each step we start a new choice to guarantee the world progresses, and we freeze c to guarantee that c progresses
seqChoice : Name → 𝕎· → ℕ → 𝕎·
seqChoice c w 0 = w
seqChoice c w (suc n) = freeze· c (startNewChoice Resℕ (seqChoice c w n)) (ℕ→ℂ· 0)
--}


{--
chainChoice-prop-aux : (n : ℕ) (s : ℕ → 𝕎·) (ind : (m : ℕ) → m < n →  s m ⊑· s (suc m)) → s 0 ⊑· s n
chainChoice-prop-aux ℕ.zero s ind = ⊑-refl· (s 0)
chainChoice-prop-aux (suc n) s ind = ⊑-trans· (chainChoice-prop-aux n s λ m x → ind m (<-trans x (n<1+n n))) (ind n (n<1+n n))
--}


{--
-- creates a chain by starting new choices at each step
chainChoice : (w : 𝕎·) → chain w
chainChoice w = mkChain s i p q
  where
    c : Name
    c = newChoice· w

    s : ℕ → 𝕎·
    s = seqChoice c (startChoice· c Resℕ w)

    i : w ⊑· s 0
    i = fst (startNewChoice⊏· Resℕ w)

    p' : (n : ℕ) → ((m : ℕ) → m < n →  s m ⊑· s (suc m)) → s n ⊑· s (suc n)
    p' n ind = ⊑-trans· (fst (startNewChoice⊏· Resℕ (s n)))
                        (freeze⊑· c (startNewChoice Resℕ (s n)) (NUM 0) comp λ n → 0 , refl)
       where
         comp : compatible· (newChoice· w) (startNewChoice Resℕ (s n)) Resℕ
         comp = ⊑-compatible· (⊑-trans· (chainChoice-prop-aux n s ind) (fst (startNewChoice⊏· Resℕ (s n))))
                              (startChoiceCompatible· Resℕ w)

    p : (n : ℕ) → s n ⊑· s (suc n)
    p n = <ℕind (λ n → s n ⊑· s (suc n)) p' n

    prog : (c : Name) (n : ℕ) → progress· c (s n) (s (suc n))
    prog c n = {!freezeProgress· c ? ?!}

    q : (c : Name) (n : ℕ) {r : Res{0ℓ}} → compatible· c (s n) r → Σ ℕ (λ m → n < m × progress· c (s n) (s m))
    q c n {r} comp = suc n , (n<1+n n) , prog c n
--}




{--
data atBethBar {w : 𝕎·} {f : wPred w} (i : inBethBar w f) : (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
data atBethBar {w} {f} i where
  ATBETHBAR-R :  (p : f w (⊑-refl· w))
                → atBethBar {w} {f} i w (⊑-refl· w) p
  ATBETHBAR-B : (w1 : 𝕎·) (e1 : w ⊑· w1) (b : 𝔹.bar (fst i) w1)
                (w2 : 𝕎·) (e2 : w1 ⊑· w2) (z : w ⊑· w2)
                (p : f w2 z)
                → atBethBar {w} {f} i w2 z p --(snd i e1 b w2 e2 z)


atBethBar-refl : {w : 𝕎·} {f : wPred w} (i : inBethBar w f) (p : f w (⊑-refl· w)) → atBethBar {w} {f} i w (⊑-refl· w) p
atBethBar-refl {w} {f} i p = ATBETHBAR-R p
--}


{--
IS𝔹-fam : {w : 𝕎·} {f : wPred w} (b : IS𝔹 w) (i : inIS𝔹 b (λ w' e' → inBethBar w' (↑wPred' f e'))) → IS𝔹 w
IS𝔹-fam {w} {f} b i = mk𝔹 bar bars ext
  where
    bar : Br
    bar w' = Σ (IS𝔹Fam b) (λ F → 𝔹.bar (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) w')

    bars : (c : chain w) → BarredChain bar c
    bars c = mkBarredChain (BarredChain.w' bp') br (BarredChain.n bp' + BarredChain.n bp) e
      where
        bp : BarredChain (𝔹.bar b) c
        bp = 𝔹.bars b c

        b' : IS𝔹 (BarredChain.w' bp)
        b' = fst (i (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp) (BarredChain.w' bp) (⊑-refl· _) (𝔹.ext b (BarredChain.b bp)))

        bp' : BarredChain (𝔹.bar b') (truncateChain {w} {c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))
        bp' = 𝔹.bars b' (truncateChain {w} {c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))

        br : bar (BarredChain.w' bp')
        br = mk𝔹Fam (BarredChain.w' bp) (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp) (BarredChain.w' bp) (⊑-refl· _) (𝔹.ext b (BarredChain.b bp)) ,
             BarredChain.b bp'

        e : BarredChain.w' bp' ⊑· chain.seq c (BarredChain.n bp' + BarredChain.n (𝔹.bars b c))
        e = BarredChain.ext bp'

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (IS𝔹Fam.z F) (𝔹.ext (fst (i (IS𝔹Fam.e1 F) (IS𝔹Fam.br F) (IS𝔹Fam.w2 F) (IS𝔹Fam.e2 F) (IS𝔹Fam.z F))) b')
--}



{--
record IS𝔹In {w : 𝕎·} (b : IS𝔹 w) : Set(L) where
  constructor mk𝔹In
  field
    w1 : 𝕎·
    e1 : w ⊑· w1
    br : 𝔹.bar b w1
--}


{--
IS𝔹-fam2 : {w : 𝕎·} (b : IS𝔹 w)
            (G : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → IS𝔹 w' → Set(lsuc(L)))
            (i : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → Σ (IS𝔹 w') (λ b' → G e ib b'))
            → IS𝔹 w
IS𝔹-fam2 = 𝔹fam2 {IS𝔹bars} IS𝔹barsFam2
--}


{--
IS𝔹-fam2 : {w : 𝕎·} (b : IS𝔹 w)
            (G : {w' : 𝕎·} (e : w ⊑· w') → IS𝔹 w' → Set(lsuc(L)))
            (i : {w' : 𝕎·} (e : w ⊑· w') (ib : 𝔹.bar b w') → Σ (IS𝔹 w') (λ b' → G e b'))
            → IS𝔹 w
IS𝔹-fam2 {w} b G i = mk𝔹 bar bars ext mon
  where
    bar : Br
    bar w' = Σ (𝔹In b) (λ F → 𝔹.bar (fst (i (𝔹In.e1 F) (𝔹In.br F))) w')

    bars : (c : pchain w) → BarredChain bar (pchain.c c)
    bars c = mkBarredChain (BarredChain.w' bp') br (BarredChain.n bp' + BarredChain.n bp) e
      where
        bp : BarredChain (𝔹.bar b) (pchain.c c)
        bp = 𝔹.bars b c

        b' : IS𝔹 (BarredChain.w' bp)
        b' = fst (i (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp))

        bp' : BarredChain (𝔹.bar b') (truncateChain {w} {pchain.c c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))
        bp' = 𝔹.bars b' (truncatePChain {w} {c} {BarredChain.n bp} {BarredChain.w' bp} (BarredChain.ext bp))

        br : bar (BarredChain.w' bp')
        br = mk𝔹In (BarredChain.w' bp) (𝔹.ext b (BarredChain.b bp)) (BarredChain.b bp) ,
             BarredChain.b bp'

        e : BarredChain.w' bp' ⊑· chain.seq (pchain.c c) (BarredChain.n bp' + BarredChain.n (𝔹.bars b c))
        e = BarredChain.ext bp'

    ext  : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (F , b') = ⊑-trans· (𝔹In.e1 F) (𝔹.ext (fst (i (𝔹In.e1 F) (𝔹In.br F))) b')

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (F , b) = F , 𝔹.mon (fst (i (𝔹In.e1 F) (𝔹In.br F))) e b
--}


--    atBethBar
--    atBethBar-refl

\end{code}
