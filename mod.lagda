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


module mod {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)
open import bar(W)



record Mod : Set(lsuc(lsuc(L))) where
  constructor mkMod
  field
    -- ## Operators
    □             : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
    □'            : (w : 𝕎·) {g : wPred w} (h : □ w g) (f : wPredDep g) → Set(lsuc(L))

    -- ## Axioms
    -- Monotonicity of the operators
    ↑□            : {w : 𝕎·} {f : wPred w} (i : □ w f) {w' : 𝕎·} (e : w ⊑· w') → □ w' (↑wPred f e)
    ↑'□           : {w : 𝕎·} {f : wPred w} (i : □ w f) {w' : 𝕎·} (e : w ⊑· w') → □ w' (↑wPred' f e)
    ↑□'           : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : □ w f) {w' : 𝕎·} (e : w ⊑· w')
                        → □' w i g → □' w' (↑□ i e) (↑wPredDep g e)

    -- axiom K: □(A→B)→□A→□B
    □Func         : {w : 𝕎·} {f g : wPred w}
                        → □ w (λ w' e' → f w' e' → g w' e')
                        → □ w f → □ w g
    -- similar to axiom K??
    ∀𝕎-□Func    : {w : 𝕎·} {f g : wPred w}
                        → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
                        → □ w f → □ w g
    -- □ → □'
    □-□'      : {w : 𝕎·} {f : wPred w} {g : wPredDep f}
                        → □ w (λ w' e' → (x : f w' e') → g w' e' x)
                        → (i : □ w f) → □' w i g
    -- similar to above without □
    ∀𝕎-□-□' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : □ w f)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') {--(at : atBar i w' e' x)--} → g w' e' x)
                        → □' w i g

    -- name?
    ∀𝕎-□        : {w : 𝕎·} {f : wPred w} → ∀𝕎 w f → □ w f

    -- □□A→□A name?
    □-idem        : {w : 𝕎·} {f : wPred w}
                        → □ w (λ w' e' → □ w' (↑wPred' f e'))
                        → □ w f
    -- similar to above
    □'-idem       : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : □ w f)
                        → □ w (λ w' e' → □' w' (↑'□ i e') (↑wPredDep' g e'))
                        → □' w i g

    -- □' → □
    ∀𝕎-□'-□ : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w} (i : □ w f)
                        → ∀𝕎 w (λ w' e' → (x : f w' e') {--→ atBar i w' e' x--} → g w' e' x → h w' e')
                        → □' w i g → □ w h

    -- (A→B→C) → □'A→□'B→□'C
    □'-comb-change : {w : 𝕎·} {f₁ f₂ f₃ : wPred w}
                         {g₁ : wPredDep f₁} {g₂ : wPredDep f₂} {g₃ : wPredDep f₃}
                         (i₁ : □ w f₁) (i₂ : □ w f₂) (i₃ : □ w f₃)
                         → ∀𝕎 w (λ w' e' → (x₁ : f₁ w' e') (x₂ : f₂ w' e') (x₃ : f₃ w' e')
                                          → g₁ w' e' x₁ → g₂ w' e' x₂ → g₃ w' e' x₃)
                         → □' w i₁ g₁ → □' w i₂ g₂ → □' w i₃ g₃

    -- □A→A some version of T?
    □-const       : {w : 𝕎·} {t : Set(lsuc(L))} → □ w (λ w e → t) → t

    -- TODO: derivable from the others?
    -- □A→□∀A some version of T?
    →□∀𝕎 : {w : 𝕎·} {f : wPred w} → □ w f → □ w (λ w' e → ∀𝕎 w' (↑wPred f e))


--    atBar             : {w : 𝕎·} {f : wPred w} (i : □ w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
--    atBar-refl        : {w : 𝕎·} {f : wPred w} (i : □ w f) (p : f w (⊑-refl· w)) → atBar {w} {f} i w (⊑-refl· w) p

--    wPredDepExtIrrBar : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : □ w f) → Set(lsuc(L))
--    atBar             : {w : 𝕎·} {f : wPred w} (i : □ w f) (w' : 𝕎·) → Set(lsuc(L))
{--    ↑□'           : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : □ w f) {w' : 𝕎·} (e : w' ⊇ w) {h : wPredDep (↑wPred f e)}
                        → ∀𝕎 w' (λ w'' e'' → (x y : f w'' (⊑-trans· e e'')) (at : atBar i w'' (⊑-trans· e e'') x) → g w'' (⊑-trans· e e'') x → h w'' e'' y)
                        → □' w i g → □' w' (↑□ i e) h--}

{--    □'-□'      : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPredDep f} (i : □ w f)
                         → wPredDepExtIrrBar g i
                         → wPredDepExtIrrBar h i
                         → □' w i (λ w' e' z → g w' e' z → h w' e' z)
                         → □' w i g → □' w i h--}

{--    □-mon         : {w2 w1 : 𝕎·} {f : wPred w1} (e : w2 ⊇ w1)
                        → □ w1 f → □ w2 (↑wPred f e)
    □'-mon        : {w2 w1 : 𝕎·} {f : wPred w1} {g : wPredDep f} (e : w2 ⊇ w1) (i : □ w1 f)
                        → □' w1 i g → □' w2 (□-mon e i) (↑wPredDep' g e)--}

{--    □-idem2       : {w : 𝕎·} {f : wPred w}
                        → wPredExtIrr f
                        → □ w (λ w' e' → □ w' (↑wPred f e'))
                        → □ w f--}
{--    □'-idem2      : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : □ w f)
                        → wPredDepExtIrrBar g i
                        → □ w (λ w' e' → □' w' (↑□ i e') (↑wPredDep g e'))
                        → □' w i g--}
{--    ∀𝕎-□'-□ : {w : 𝕎·} {f : wPred w} {g : wPredDep f} {h : wPred w}
                        → ∀𝕎 w (λ w' e' → (x : f w' e') → g w' e' x → h w' e')
                        → (i : □ w f) → □' w i g → □ w h--}
{--    □'-change     : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i j : □ w f)
                        → ∀𝕎 w (λ w' e' → (x y : f w' e') → atBar i w' e' x → atBar j w' e' y → g w' e' x → g w' e' y)
                        → □' w i g → □' w j g--}
    -- a more general version



□'-comb : (b : Mod) {w : 𝕎·} {f : wPred w} {g h k : wPredDep f} (i : Mod.□ b w f)
              → ∀𝕎 w (λ w' e' → (z zg zh : f w' e')
                               → g w' e' zg → h w' e' zh → k w' e' z)
              → Mod.□' b w i g → Mod.□' b w i h → Mod.□' b w i k
□'-comb b {w} {f} {g} {h} {k} i aw j₁ j₂ =
  Mod.□'-comb-change b i i i (λ w1 e1 x₁ x₂ x₃ a b → aw w1 e1 x₃ x₁ x₂ a b) j₁ j₂


□'-change : (b : Mod) {w : 𝕎·} {f k : wPred w} {g : wPredDep f} {h : wPredDep k} (i : Mod.□ b w f) (j : Mod.□ b w k)
                → ∀𝕎 w (λ w' e' → (x : f w' e') (y : k w' e')
                                  → g w' e' x → h w' e' y)
                → Mod.□' b w i g → Mod.□' b w j h
□'-change b {w} {f} {k} {g} {h} i j aw u =
  Mod.□'-comb-change b i i j (λ w1 e1 x₁ x₂ x₃ a b → aw w1 e1 x₁ x₃ a) u u


-- This is a consequence of [∀𝕎-□'-□]
□'-□ : (b : Mod) {w : 𝕎·} {f : wPred w} {h : wPred w}
               → (i : Mod.□ b w f) → Mod.□' b w i (λ w1 e1 z → h w1 e1) → Mod.□ b w h
□'-□ b {w} {f} {h} i q = Mod.∀𝕎-□'-□ b i (λ w1 e1 x {--at--} z → z) q


-- This is a consequence of [□'-comb] for 3 dependent bars
□'3 : (b : Mod) {w : 𝕎·} {f : wPred w} {g h k j : wPredDep f} (i : Mod.□ b w f)
          → ∀𝕎 w (λ w' e' → (z : f w' e') (zg : f w' e') (zh : f w' e') (zk : f w' e')
                             → g w' e' zg → h w' e' zh → k w' e' zk → j w' e' z)
          → Mod.□' b w i g → Mod.□' b w i h → Mod.□' b w i k → Mod.□' b w i j
□'3 b {w} {f} {g} {h} {k} {j} i imp ig ih ik = c
  where
    ip : Mod.□' b w i (λ w1 e1 z → Σ (f w1 e1) λ zg → Σ (f w1 e1) λ zh → g w1 e1 zg × h w1 e1 zh)
    ip = □'-comb b i (λ w1 e1 z zg zh xg xh → zg , zh , xg , xh) ig ih

    c : Mod.□' b w i j
    c = □'-comb b i (λ w1 e1 zj zh zk (zg' , zh' , ig , ih) ik → imp w1 e1 zj zg' zh' zk ig ih ik) ip ik



BarsProps→Mod : BarsProps → Mod
BarsProps→Mod b =
  mkMod
    (λ w → Σ∈𝔹 (BarsProps.bars b) {w})
    (λ w → Σ∈𝔹' (BarsProps.bars b) {w})
    (↑Σ∈𝔹 (BarsProps.mon b))
    (↑'Σ∈𝔹 (BarsProps.mon b))
    (λ {w} {f} {g} → ↑Σ∈𝔹' (BarsProps.mon b) {w} {f} {g})
    (Σ∈𝔹Func (BarsProps.isect b))
    (∀𝕎-Σ∈𝔹Func {BarsProps.bars b})
    (Σ∈𝔹-Σ∈𝔹' (BarsProps.mon b))
    (∀𝕎-Σ∈𝔹-Σ∈𝔹' (BarsProps.all b))
    (∀𝕎-Σ∈𝔹 (BarsProps.all b))
    (Σ∈𝔹-idem (BarsProps.fam2 b))
    (Σ∈𝔹'-idem (BarsProps.mon b) (BarsProps.fam2 b))
    (∀𝕎-Σ∈𝔹'-Σ∈𝔹 (BarsProps.fam2 b))
--    (Σ∈𝔹'-comb (BarsProps.mon b) (BarsProps.isect b) (BarsProps.fam2 b))
--    (Σ∈𝔹'-change (BarsProps.mon b) (BarsProps.isect b) (BarsProps.fam2 b))
    (Σ∈𝔹'-comb-change (BarsProps.mon b) (BarsProps.isect b) (BarsProps.fam2 b))
    (Σ∈𝔹-const (BarsProps.ex b))
    →Σ∈𝔹∀𝕎
\end{code}
