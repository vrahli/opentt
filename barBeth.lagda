\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc ; _⊔_ to _∨_)
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
open import compatible
open import progress


-- Choice is only needed for Beth bars to build an infinite sequence of worlds
module barBeth {L : Level} (W : PossibleWorlds {L})
               (C : Choice) (M : Compatible {L} W C) (P : Progress {L} W C M)
       where
open import worldDef{L}(W)
open import bar{L}{L ∨ 1ℓ}(W)
open import mod{L}{L ∨ 1ℓ}(W)
-- open import nucleus{L ∨ 1ℓ}(W)

-- Those are only needed by the Beth instance
open import choiceDef{L}(C)
open import compatibleDef(W)(C)(M)
open import progressDef(W)(C)(M)(P)


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
record BarredChain (bar : Br) {w : 𝕎·} (c : chain w) : Set L where
  constructor mkBarredChain
  field
    w'  : 𝕎·
    b   : bar w'
    n   : ℕ
    ext : w' ⊑· chain.seq c n


IS𝔹bars : Bars
IS𝔹bars w bar = (c : pchain w) → BarredChain bar (pchain.c c)

{--

Currently we cannot turn this into a nucleus due to the jump in universe level.
If there is some way to postulate $n ∨ 1ℓ = n$ then we could try doing this inside a module.

-- Open Bars give a nucleus (when restricted to upward closed subsets)
j : UCSubset → UCSubset
j (U , U-UC) = (λ w → IS𝔹bars w U) , (λ w1⊑w2 w1◀U w3 w2⊑w3 → w1◀U w3 (⊑-trans· w1⊑w2 w2⊑w3))

IS𝔹-mono : (U V : UCSubset) → U ⋐ V → j U ⋐ j V
IS𝔹-mono U V U⋐V w◀U w1 w⊑w1 = let (w2 , w1⊑w2 , w2∈U) = w◀U w1 w⊑w1 in w2 , w1⊑w2 , U⋐V w2∈U

IS𝔹-well-defined : well-defined j
IS𝔹-well-defined = λ U V (U⋐V , V⋐U) → IS𝔹-mono U V U⋐V , IS𝔹-mono V U V⋐U

IS𝔹-extensive : extensive j
IS𝔹-extensive (U , U-UC) w∈U w1 w⊑w1 = w1 , ⊑-refl· w1 , U-UC w⊑w1 w∈U

IS𝔹-idempotent : idempotent j
IS𝔹-idempotent U w◀◀U w1 w⊑w1 = let (w2 , w1⊑w2 , w2◀U) = w◀◀U w1 w⊑w1
                                   (w3 , w2⊑w3 , w3∈U) = w2◀U w2 (⊑-refl· w2)
                                in (w3 , ⊑-trans· w1⊑w2 w2⊑w3 , w3∈U )

IS𝔹-meet-preserving : meet-preserving j
IS𝔹-meet-preserving U V = jU⋒V⋐jU⋒jV , jU⋒jV⋐jU⋒V
  where
    jU⋒V⋐jU⋒jV : j (U ⋒ V) ⋐ j U ⋒ j V
    jU⋒V⋐jU⋒jV = ⋒-intro {j U} {j V} {j (U ⋒ V)} (IS𝔹-mono (U ⋒ V) U (⋒-elim-l {U} {V}))
                                                 (IS𝔹-mono (U ⋒ V) V (⋒-elim-r {U} {V}))

    jU⋒jV⋐jU⋒V : j U ⋒ j V ⋐ j (U ⋒ V)
    jU⋒jV⋐jU⋒V (w◀U , w◀V) w1 w⊑w1 = let U-UC = snd U
                                         (w2 , w1⊑w2 , w2∈U) = w◀U w1 w⊑w1
                                         (w3 , w2⊑w3 , w3∈V) = w◀V w2 (⊑-trans· w⊑w1 w1⊑w2)
                                      in w3 , ⊑-trans· w1⊑w2 w2⊑w3 , U-UC w2⊑w3 w2∈U , w3∈V

IS𝔹-inhabited : inhabited j
IS𝔹-inhabited {w} U w◀U = let (w1 , _ , w1∈U) = w◀U w (⊑-refl· w) in w1 , w1∈U

IS𝔹-cucleus : isCuclear j
IS𝔹-cucleus = mkCucleus IS𝔹-inhabited (mkNucleus IS𝔹-well-defined IS𝔹-extensive IS𝔹-idempotent IS𝔹-meet-preserving)

--}

-- a Beth bar where all infinite sequences are barred
IS𝔹 : 𝕎· → Set (2ℓ ∨ lsuc L)
IS𝔹 w = 𝔹 IS𝔹bars w

inBethBar : ∀ {r} (w : 𝕎·) (f : wPred {r} w) → Set (2ℓ ∨ lsuc L ∨ r)
inBethBar w = Σ∈𝔹 IS𝔹bars {w}

inBethBar' : ∀ {r} (w : 𝕎·) {g : wPred {r} w} (h : inBethBar w g) (f : wPredDep g) → Set (2ℓ ∨ lsuc L ∨ r)
inBethBar' w = Σ∈𝔹' IS𝔹bars {w}



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


{--IS𝔹barsFam1 : BarsFam1 IS𝔹bars
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
--}



IS𝔹barsFam2 : BarsFam2 IS𝔹bars
IS𝔹barsFam2 {_} {w} b G i c =
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
--    IS𝔹barsFam1
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
inBethBar-Mod : Mod
inBethBar-Mod = BarsProps→Mod IS𝔹BarsProps
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

inIS𝔹 : ∀ {r} {w : 𝕎·} (b : IS𝔹 w) (f : wPred {r} w) → Set (L ∨ r)
inIS𝔹 = ∈𝔹 {_} {IS𝔹bars}






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
