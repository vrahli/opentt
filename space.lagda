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


module space {L : Level} (W : PossibleWorlds {L})
       where
open import worldDef{L}(W)

-- We start work on this mostly separate from the rest of the formalisation. This
-- is due to the fact that currently we have some issues with universe levels
-- possibly being too restrictive. As a result, we might redefine a lot.

-- A bar is any subset of worlds
Bar : Set(lsuc(L))
Bar = 𝕎· → Set(L)

-- Containment of worlds in a bar
_∈_ : 𝕎· → Bar → Set(L)
_∈_ w U = U w
infix 20 _∈_

-- The type of overing relations, however arbitrary.
-- Examples of inhabitants we are interested in are the
-- Kripke, Beth and Open barring predicates.
Cover : Set(lsuc(L))
Cover = 𝕎· → (𝕎· → Set(L)) → Set(L)

isUpwardsClosed : Bar → Set(L)
isUpwardsClosed U = {w w' : 𝕎·} → w ⊑· w' → w ∈ U → w' ∈ U

UCSubset : Set(lsuc(L))
UCSubset = Σ Bar isUpwardsClosed

_∈·_ : 𝕎· → UCSubset → Set(L)
_∈·_ w (U , _) = U w
infix 20 _∈·_

_∩_ : UCSubset → UCSubset → UCSubset
_∩_ (U , U-is-UC) (V , V-is-UC) = (λ w → w ∈ U × w ∈ V) , λ e (w∈U , w∈V) → U-is-UC e w∈U , V-is-UC e w∈V
infix 22 _∩_

_⊆_ : UCSubset → UCSubset → Set(L)
_⊆_ (U , _) (V , _) = (w : 𝕎·) → w ∈ U → w ∈ V
infix 21 _⊆_

_≅_ : UCSubset → UCSubset → Set(L)
_≅_ X Y = X ⊆ Y × Y ⊆ X
infix 21 _≅_

unital : (UCSubset → UCSubset) → Set(lsuc(L))
unital j = (X : UCSubset) → X ⊆ j X

idem : (UCSubset → UCSubset) → Set(lsuc(L))
idem j = (X : UCSubset) → j (j X) ⊆ j X

meet-preserving : (UCSubset → UCSubset) → Set(lsuc(L))
meet-preserving j = (X Y : UCSubset) → j (X ∩ Y) ≅ j X ∩ j Y

UCS-union : {I : Set(L)} (f : I → UCSubset) → UCSubset
UCS-union {I} f = (λ w → Σ I λ i → w ∈· f i) , λ e (i , w∈fi) → i , snd (f i) e w∈fi

syntax UCS-union {I} (λ i → A) = ∪[ i ∈ I ] A

overshooting : (UCSubset → UCSubset) → Set(lsuc(L))
overshooting j = {I : Set(L)} (f : I → UCSubset) → (∪[ i ∈ I ] (j (f i))) ⊆ j (∪[ i ∈ I ] (f i))

-- Traditionally a nucleus only has the first 3 properties, but in our case they
-- also always satisfy the 4th property
isNucleus : (UCSubset → UCSubset) → Set(lsuc(L))
isNucleus j = unital j × idem j × meet-preserving j × overshooting j

-- It seems that nuclei do not interact with joins in a nice way
--nucleus-unions : {j : UCSubset → UCSubset} (j-is-nucleus : isNucleus j)
--                 {I : Set(L)} (f : I → UCSubset)
--               → (∪[ i ∈ I ] (j (f i))) ⊆ j (∪[ i ∈ I ] (f i))
--nucleus-unions {j} (unit , _ , _) {I} f w (i , w∈∪jfi) = unit (∪[ i ∈ I ] (f i)) w (i , {!!})

-- In this module we check that the open bar covering relation gives a nucleus
-- the frame of upward closed subsets of worlds.
-- Similar reasoning should let us see that the Kripke and Beth covering relations
-- also give us a nucleus.
module OpenBar where

  -- The covering relation between worlds and bars
  -- Right now we focus on open bars since they are the strictest
  _◀o_ : 𝕎· → (𝕎· → Set(L)) → Set(L)
  _◀o_ w U = {w' : 𝕎·} (e : w ⊑· w') → Σ 𝕎· (λ w'' → w' ⊑· w'' × w'' ∈ U)

  -- The flipped covering relation will hopefully give us a nucleus on the set of upward closed subsets
  _o▶ : UCSubset → UCSubset
  _o▶ (U , U-is-UC) = _◀o U , λ {w1} {w2} e12 w1◀oU {w3} e23 → w1◀oU (⊑-trans· e12 e23)

  o▶-unit : unital _o▶
  o▶-unit (U , U-is-UC) w1 w1∈U {w2} e12 = w2 , ⊑-refl· w2 , U-is-UC e12 w1∈U

  o▶-idem : idem _o▶
  o▶-idem (U , U-is-UC) w1 w1∈Uo▶o▶ {w2} e12 = let (w3 , e23 , w3◂U) = w1∈Uo▶o▶ e12
                                                   (w4 , e34 , w4∈U) = w3◂U (⊑-refl· w3)
                                                  in w4 , ⊑-trans· e23 e34 , w4∈U

  o▶-meets : meet-preserving _o▶
  o▶-meets X Y = under X Y , over X Y
    where
      under : (X Y : UCSubset) → ((X ∩ Y) o▶) ⊆ ((X o▶) ∩ (Y o▶))
      under (U , U-is-UC) (V , V-is-UC) w1 w1◀oU∩V = w1◀oU , w1◀oV
        where
          w1◀oU : w1 ◀o U
          w1◀oU {w2} e12 = let (w3 , e23 , w3∈U , w3∈V) = w1◀oU∩V e12 in w3 , e23 , w3∈U

          w1◀oV : w1 ◀o V
          w1◀oV {w2} e12 = let (w3 , e23 , w3∈U , w3∈V) = w1◀oU∩V e12 in w3 , e23 , w3∈V

      over : (X Y : UCSubset) → ((X o▶) ∩ (Y o▶)) ⊆ ((X ∩ Y) o▶)
      over (U , U-is-UC) (V , V-is-UC) w1 (w1◀oU , w1◀oV) {w2} e12 =
        let (w3 , e23 , w3∈U) = w1◀oU e12
            (w4 , e34 , w4∈V) = w1◀oV (⊑-trans· e12 e23)
        in w4 , ⊑-trans· e23 e34 , U-is-UC e34 w3∈U , w4∈V

  o▶-over : overshooting _o▶
  o▶-over {I} f w1 (i , w1◀ofi) {w2} e12 = let (w3 , e23 , w3∈fi) = w1◀ofi e12
                                           in   w3 , e23 , i , w3∈fi

  o▶-isNucleus : isNucleus _o▶
  o▶-isNucleus = o▶-unit , o▶-idem , o▶-meets , o▶-over


-- Now we are interested in whether starting with a covering relation that gives
-- a nucleus is enough to get the desired properties from `bar.lagda`
-- NB: Since we are assuming we have a nucleus on the upward closed subsets, it
--     seems likely that we should modify the properties slightly to only work
--     with monotone bars (which are the same as upward closed subsets)

restricts-to-UCS : Cover → Set(lsuc(L))
restricts-to-UCS _◀_ = (U : Bar) → isUpwardsClosed U → isUpwardsClosed (_◀ U)

rest : {_◀_ : Cover} → restricts-to-UCS _◀_ → UCSubset → UCSubset
rest {_◀_} h (U , U-is-UC) = (_◀ U) , h U U-is-UC

gives-nucleus : {_◀_ : Cover} (h : restricts-to-UCS _◀_) → Set(lsuc(L))
gives-nucleus h = isNucleus (rest h)

module nucleusIsGood
  {_◀_ : Cover}
  {◀-respects-UCS : restricts-to-UCS _◀_}
  (◀-nucleus : gives-nucleus ◀-respects-UCS)
  where

  _◀·_ : 𝕎· → UCSubset → Set(L)
  _◀·_ w (U , _) = U w

  _▶ : UCSubset → UCSubset
  _▶ = rest ◀-respects-UCS

  ▶-unit : unital _▶
  ▶-unit = fst ◀-nucleus

  ▶-mult : idem _▶
  ▶-mult = fst (snd ◀-nucleus)

  ▶-meets : meet-preserving _▶
  ▶-meets = fst (snd (snd ◀-nucleus))

  ▶-over : overshooting _▶
  ▶-over = snd (snd (snd ◀-nucleus))

  {-- Intersection --}
  Bars∩ : (_◀_ : Cover) → Set(lsuc(L))
  Bars∩ _◀_ =
    {w : 𝕎·} (X Y : UCSubset)
    → w ◀ (fst X)
    → w ◀ (fst Y)
    → w ◀ (fst (X ∩ Y))

  ◀-Bars∩ : Bars∩ _◀_
  ◀-Bars∩ {w} U V w◀U w◀V = (snd (▶-meets U V)) w (w◀U , w◀V)

  {-- Monotonicity --}
  Bars⊑ : (_◀_ : Cover) → Set(lsuc(L))
  Bars⊑ _◀_ =
    {w1 w2 : 𝕎·} (e : w1 ⊑· w2) (X : UCSubset)
    → w1 ◀ (fst X)
    → w2 ◀ (fst X)

  ◀-Bars⊑ : Bars⊑ _◀_
  ◀-Bars⊑ e12 (U , U-is-UC) w1◀U = ◀-respects-UCS U U-is-UC e12 w1◀U

  {-- Top --}
  bar∀ : 𝕎· → UCSubset
  bar∀ w0 = w0 ⊑·_ , λ w1⊑w2 w0⊑w1 → ⊑-trans· w0⊑w1 w1⊑w2

  -- Notice the lower universe level since we are not quantifying over subsets.
  Bars∀ : (_◀_ : Cover) → Set(L)
  Bars∀ _◀_ = (w : 𝕎·) → w ∈· ((bar∀ w) ▶)

  ◀-Bars∀ : Bars∀ _◀_
  ◀-Bars∀ w = ▶-unit (bar∀ w) w (⊑-refl· w)

  {-- Unions --}
  barFam2Test : {_◀_ : Cover} {w : 𝕎·} (U : UCSubset) (w◀U : w ◀ (fst U))
                (G : {w' : 𝕎·} (w'∈U : w' ∈· U) (V : UCSubset) → w' ◀ (fst V) → Set(L))
                (i : {w' : 𝕎·} (w'∈U : w' ∈· U) → Σ UCSubset (λ V → Σ (w' ◀ (fst V)) (λ w'◀V → G w'∈U V w'◀V)))
                → UCSubset
  barFam2Test {B} {w} U w◀U G i = (λ w0 → Σ 𝕎· λ w1 → Σ (w1 ∈· U) λ w1∈U → w0 ∈· fst (i w1∈U))
                                , λ {w1} {w2} e12 (w3 , w3∈U , w1∈iw3∈U) → w3 , w3∈U , {!snd (i w3∈U) ?!}

  -- BarsFam2Test : (_◀_ : Cover) → Set(lsuc(L))
  -- BarsFam2Test _◀_ =
  --   {w : 𝕎·} (U : UCSubset) (w◀U : w ◀ (fst U))
  --   (G : {w' : 𝕎·} (w'∈U : w' ∈· U) (V : UCSubset) → w' ◀ (fst V) → Set(L))
  --   (i : {w' : 𝕎·} (w'∈U : w' ∈· U) → Σ UCSubset (λ V → Σ (w' ◀ (fst V)) (λ w'◀V → G w'∈U V w'◀V)))
  --   → w ◀ barFam2Test U w◀U G i

  -- the bar U covers w.
  -- Let V be the union of bars given above
  -- know that for any element w0 inside the bar U, we have some bar U0 covering w0.
  --
  -- we know that (how do we show this)
  --   U ⊆ (union.i U_i) ▶
  -- so
  --   U ▶ ⊆ (union.i U_i) ▶▶ ⊆ (union.i U_i) ▶
  -- As w ◀ U, then w ◀ union.i U_i too
  --
  --
  -- WRONG:
  -- so for any element w0 inside the bar U, we know that w is in (U0 ▶▶), hence it is in U0 ▶
  -- hence w is covered by all the bars we are unioning, so if we can show that
  --     union_i (U_i ▶) ⊆ (union.i U_i) ▶
  -- (this is definitely the case for the covering relations we have so far, but I don't think it is a result of being a nucleus)
  --
  -- maybe can show
  --     j (union_i (j U_i)) ⊆ j j (union U_i)
  -- so then
  --     union_i (j U_i) ⊆ j (union_i (j U_i)) ⊆ j j (union_i U_i) ⊆ j (union_i U_i)

  -- ◀-BarsFam2Test : BarsFam2Test _◀_
  -- ◀-BarsFam2Test {w} U w◀U G i = {!!}
  --   where
  --     foo : U ⊆ ((barFam2Test U w◀U G i) ▶)
  --     foo = ?

  {-- Inhabitation --}
  -- This is not derivable from our covering giving a nucleus. To see why,
  -- consider the covering relation which accepts any subset.
  Bars∃ : (_◀_ : Cover) → Set(lsuc(L))
  Bars∃ _◀_ =
    {w : 𝕎·} {U : UCSubset} (w◀U : w ◀· U) (ext : {w' : 𝕎·} → w' ∈· U → w ⊑· w')
    → Σ 𝕎· λ w' → w ⊑· w' × w' ∈· U

  -- ◀-Bars∃ : Bars∃ _◀_
  -- ◀-Bars∃ {w} {(U , U-is-UC)} w◀U ext = {!!}




\end{code}
