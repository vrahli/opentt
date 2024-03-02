\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst ; cong)
--open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
--open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
--open import Agda.Builtin.String
--open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
--open import Function.Inverse using (Inverse)
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import terms


module worldInstanceRef3 (E : Extensionality 0ℓ 0ℓ) where

true≠false : ¬ true ≡ false
true≠false ()


⊎bool : (b : Bool) → b ≡ true ⊎ b ≡ false
⊎bool true = inj₁ refl
⊎bool false = inj₂ refl


_≡ᵇ_ : (a b : Bool) → a ≡ b ⊎ ¬ a ≡ b
false ≡ᵇ false = inj₁ refl
false ≡ᵇ true = inj₂ (λ ())
true ≡ᵇ false = inj₂ (λ ())
true ≡ᵇ true = inj₁ refl
\end{code}



This provides an instance of world and choice for choice sequences


\begin{code}
B→C : Bool → CTerm
B→C true = #BTRUE
B→C false = #BFALSE


-- We could use Bools instead but then in choiceBarInstance.lagda, we have to pick a better type that contains only choices.
-- Could instead ∈Typeℂ₀₁→ in choiceBar have an assumption about a and b being choices?
open import choice

¬seq-choice : (c : Bool) → #¬Seq (B→C c)
¬seq-choice true  = refl
¬seq-choice false = refl

¬enc-choice : (c : Bool) → #¬Enc (B→C c)
¬enc-choice true  = refl
¬enc-choice false = refl

choiceRef : Choice
choiceRef = mkChoice Bool B→C ¬seq-choice ¬enc-choice --B→C-inj

open import choiceDef{1ℓ}(choiceRef)


-- The Bool says whether the cell is "frozen"
record Cell : Set₁ where
  constructor cell
  field
    name : Name
    r : Res{0ℓ}
    v : Maybe ℂ·


-- Worlds - entries are added at the end of the list
world : Set₁
world = List Cell


wdom : world → List Name
wdom [] = []
wdom (cell name _ _ ∷ w) = name ∷ wdom w


wnames : world → List Name
wnames w = []


remNRes : {L : Level} (n : Name) (l : List (NRes{L})) → List (NRes{L})
remNRes {L} n [] = []
remNRes {L} n (r ∷ l) with n ≟ NRes.name r
... | yes p = remNRes n l
... | no p = r ∷ remNRes n l


wrdom : world → List NRes
wrdom [] = []
wrdom (cell name r v ∷ w) = mkNRes name r ∷ remNRes name (wrdom w)


update : (n : Name) (v : ℂ·) (w : world) → world
update _ _ [] = []
-- We leave 'just' cells alone
update n v (cell name r (just x) ∷ w) with n ≟ name
... | yes p = cell name r (just x) ∷ w
... | no  p = cell name r (just x) ∷ update n v w
-- We might update a 'nothing' cell
update n v (cell name r nothing ∷ w) with n ≟ name
... | yes p = cell name r (just v) ∷ w
... | no  p = cell name r nothing ∷ update n v w


newCell : (n : Name) (r : Res{0ℓ}) (w : world) → world
newCell n r w = cell n r nothing ∷ w


getRef : Name → world → Maybe Cell
getRef name [] = nothing
getRef name (cell n r v ∷ w) with name ≟ n
... | yes p = just (cell n r v)
... | no p = getRef name w


Mℂ· : Set
Mℂ· = Maybe ℂ·


∈world : (n : Name) (r : Res{0ℓ}) (v : Mℂ·) (w : world) → Set₁
∈world n r v w = getRef n w ≡ just (cell n r v)


hasRes : (c : Name) (w : world) (r : Res{0ℓ}) → Set₁
hasRes c w r = Σ Mℂ· (λ v → ∈world c r v w)


data _≼_ : (w2 : world) (w1 : world) → Set₁ where
  ≼-refl  : (w : world) → w ≼ w
  ≼-trans : {w1 w2 w3 : world} → w1 ≼ w2 → w2 ≼ w3 → w1 ≼ w3
  upd     : (w : world) (n : Name) (r : Res{0ℓ}) (v : ℂ·)
          → hasRes n w r
          → ⋆ᵣ r v
          → w ≼ update n v w
  new     : (w : world) (n : Name) (r : Res{0ℓ})
          → ¬ (n ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
          → w ≼ newCell n r w


open import world

PossibleWorldsRef : PossibleWorlds
PossibleWorldsRef = mkPossibleWorlds world _≼_ ≼-refl ≼-trans

open import worldDef(PossibleWorldsRef)


resSatRef : (v : Mℂ·) (r : Res{0ℓ}) → Set
resSatRef nothing r = ⊤
resSatRef (just v) r = ⋆ᵣ r v


-- This is the same as 'hasRef' & enforces satisfiability too
compatibleRef : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set₁
compatibleRef c w r = Σ Mℂ· (λ v → ∈world c r v w × resSatRef v r)


pres-resSatRef : (v v' : Mℂ·) (r : Res{0ℓ}) → Set
pres-resSatRef v v' r = resSatRef v r → resSatRef v' r


pres-resSatRef-refl : (v : Mℂ·) (r : Res{0ℓ}) → pres-resSatRef v v r
pres-resSatRef-refl v r d = d


pres-resSatRef-trans : {v1 v2 v3 : Mℂ·} {r : Res{0ℓ}}
                     → pres-resSatRef v1 v2 r
                     → pres-resSatRef v2 v3 r
                     → pres-resSatRef v1 v3 r
pres-resSatRef-trans {v1} {v2} {v3} {r} p1 p2 s = p2 (p1 s)


satFrozen : (r : Res{0ℓ}) (v v' : Mℂ·) → Set
satFrozen r (just v) (just v') = v ≡ v'
satFrozen r (just v) nothing   = ⊥
satFrozen r nothing  x         = ⊤


satFrozen-refl : (r : Res{0ℓ}) (v : Mℂ·) → satFrozen r v v
satFrozen-refl r (just x) = refl
satFrozen-refl r nothing = tt


satFrozen-trans : {r : Res{0ℓ}} {v1 v2 v3 : Mℂ·}
                → satFrozen r v1 v2
                → satFrozen r v2 v3
                → satFrozen r v1 v3
satFrozen-trans {r} {just x} {just x₁} {just x₂} s1 s2 = trans s1 s2
satFrozen-trans {r} {nothing} {v2} {v3} s1 s2 = tt


cell-inj1 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Mℂ·} → cell n1 r1 v1 ≡ cell n2 r2 v2 → n1 ≡ n2
cell-inj1 refl =  refl


cell-inj2 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Mℂ·} → cell n1 r1 v1 ≡ cell n2 r2 v2 → r1 ≡ r2
cell-inj2 refl =  refl


cell-inj3 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Mℂ·} → cell n1 r1 v1 ≡ cell n2 r2 v2 → v1 ≡ v2
cell-inj3 refl =  refl


getRef-update-just-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·)
                     → getRef name w ≡ just (cell name r (just v))
                     → getRef name (update name v' w) ≡ just (cell name r (just v))
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e with name ≟ name₁
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e | yes p
  rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e)
  with name₁ ≟ name₁
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e | yes p | yes q = refl
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e | yes p | no q = ⊥-elim (q refl)
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e | no p
  with name ≟ name₁
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e | no p | yes q = ⊥-elim (p q)
getRef-update-just-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} v' e | no p | no q = getRef-update-just-≡ {w} v' e
getRef-update-just-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} v' e
  with name ≟ name₁
getRef-update-just-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} v' e | yes p
  rewrite p
  = ⊥-elim (¬just≡nothing (sym (cell-inj3 (just-inj e))))
getRef-update-just-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} v' e | no p
  with name ≟ name₁
getRef-update-just-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} v' e | no p | yes q = ⊥-elim (p q)
getRef-update-just-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} v' e | no p | no q = getRef-update-just-≡ {w} v' e


getRef-update-just-≡' : {w : 𝕎·} {name n : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·)
                      → getRef name w ≡ just (cell name r (just v))
                      → getRef name (update n v' w) ≡ just (cell name r (just v))
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e
  with n ≟ name₁
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e | yes p
  with name ≟ name₁
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e | yes p | yes q = e
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e | yes p | no q = e
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e | no p
  with name ≟ name₁
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e | no p | yes q = e
getRef-update-just-≡' {cell name₁ r₁ (just x) ∷ w} {name} {n} {r} {v} v' e | no p | no q =
  getRef-update-just-≡' {w} {name} {n} {r} {v} v' e
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e
  with n ≟ name₁
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e | yes p
  with name ≟ name₁
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e | yes p | yes q =
  ⊥-elim (¬just≡nothing (sym (cell-inj3 (just-inj e))))
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e | yes p | no q = e
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e | no p
  with name ≟ name₁
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e | no p | yes q = e
getRef-update-just-≡' {cell name₁ r₁ nothing ∷ w} {name} {n} {r} {v} v' e | no p | no q =
  getRef-update-just-≡' {w} {name} {n} {r} {v} v' e


getRef-update-nothing-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·}
                        → getRef name w ≡ just (cell name r nothing)
                        → getRef name (update name v w) ≡ just (cell name r (just v))
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e with name ≟ name₁
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e | yes p
  rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e)
  with name₁ ≟ name₁
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e | yes p | yes q =
  ⊥-elim (¬just≡nothing (cell-inj3 (just-inj e)))
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e | yes p | no q = ⊥-elim (q refl)
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e | no p
  with name ≟ name₁
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e | no p | yes q = ⊥-elim (p q)
getRef-update-nothing-≡ {cell name₁ r₁ (just x) ∷ w} {name} {r} {v} e | no p | no q = getRef-update-nothing-≡ {w} e
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e
  with name ≟ name₁
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e | yes p
  rewrite p
  with name₁ ≟ name₁
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e | yes p | yes q
  rewrite cell-inj2 (just-inj e)
  = refl
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e | yes p | no q  = ⊥-elim (q refl)
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e | no p
  with name ≟ name₁
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e | no p | yes q = ⊥-elim (p q)
getRef-update-nothing-≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {v} e | no p | no q = getRef-update-nothing-≡ {w} e


{--
getRef-update-true-¬frz-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·) (f : Bool)
                       → ¬ (Rfrz? r)
                       → getRef name w ≡ just (cell name r v true)
                       → getRef name (update name v' f w) ≡ just (cell name r v' f)
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with Res.frz r
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | yes p | true = ⊥-elim (frz tt)
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | yes p | false with freeze₁ r v' f
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | yes p | false | true with name₁ ≟ name₁
... | yes q = refl
... | no q = ⊥-elim (q refl)
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | yes p | false | false with name₁ ≟ name₁
... | yes q = refl
... | no q = ⊥-elim (q refl)
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | no p with name ≟ name₁
... |    yes q = ⊥-elim (p q)
... |    no q = getRef-update-true-¬frz-≡ {w} v' f frz e



getRef-update-false-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·) (f : Bool)
                      → freeze₁ r v' f ≡ true
                      → getRef name w ≡ just (cell name r v false)
                      → getRef name (update name v' f w) ≡ just (cell name r v' f)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e with name ≟ name₁
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p
  rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name₁ ≟ name₁
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p | yes q with Res.frz r
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p | yes q | true with freeze₁ r v' f
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p | yes q | true | true with name₁ ≟ name₁
... | yes z  = refl
... | no z  = ⊥-elim (z refl)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p | yes q | true | false with name₁ ≟ name₁
... | yes z  = ⊥-elim (true≠false (sym fr))
... | no z  = ⊥-elim (z refl)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p | yes q | false with name₁ ≟ name₁
... | yes z = refl
... | no z = ⊥-elim (z refl)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | yes p | no q = ⊥-elim (q refl)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f fr e | no p with name ≟ name₁
...     | yes q = ⊥-elim (p q)
...     | no q = getRef-update-false-≡ {w} v' f fr e


getRef-update-false-≡′ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·) (f : Bool)
                       → Res.frz r ≡ true
                       → freeze₁ r v' f ≡ false
                       → getRef name w ≡ just (cell name r v false)
                       → getRef name (update name v' f w) ≡ just (cell name r v false)
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e with name ≟ name₁
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p
  rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name₁ ≟ name₁
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p | yes q with Res.frz r
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p | yes q | true with freeze₁ r v' f
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p | yes q | true | true with name₁ ≟ name₁
... | yes z  = ⊥-elim (true≠false fr)
... | no z  = ⊥-elim (z refl)
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p | yes q | true | false with name₁ ≟ name₁
... | yes z  = refl
... | no z  = ⊥-elim (z refl)
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p | yes q | false with name₁ ≟ name₁
... | yes z = ⊥-elim (true≠false (sym frr))
... | no z = ⊥-elim (z refl)
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | yes p | no q = ⊥-elim (q refl)
getRef-update-false-≡′ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frr fr e | no p with name ≟ name₁
...     | yes q = ⊥-elim (p q)
...     | no q = getRef-update-false-≡′ {w} v' f frr fr e
--}


getRef-update-¬≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : Mℂ·} (name' : Name) (v' : ℂ·)
                 → ¬ name' ≡ name
                 → getRef name w ≡ just (cell name r v)
                 → getRef name (update name' v' w) ≡ just (cell name r v)
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {nothing} name' v' d e
 with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {nothing} name' v' d e | yes p
  rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e)
  with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {nothing} name' v' d e | yes p | yes q
  rewrite q = ⊥-elim (d refl)
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {nothing} name' v' d e | yes p | no q
  with name₁ ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {nothing} name' v' d e | yes p | no q | yes s = refl
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {nothing} name' v' d e | yes p | no q | no s = ⊥-elim (s refl)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p
  with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p | yes q
  rewrite q
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p | yes q | yes s = ⊥-elim (p s)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p | yes q | no s = e
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p | no q
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p | no q | yes s = ⊥-elim (p s)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {nothing} name' v' d e | no p | no q | no s =
  getRef-update-¬≡ {w} {name} {r} {nothing} name' v' d e
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p
  with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p | yes q
  rewrite q
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p | yes q | yes s = ⊥-elim (p s)
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p | yes q | no s = e
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p | no q
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p | no q | yes s
  rewrite s = ⊥-elim (p refl)
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {nothing} name' v' d e | no p | no q | no s =
  getRef-update-¬≡ {w} {name} {r} {nothing} name' v' d e
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | yes p
  rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e)
  with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | yes p | yes q
  rewrite q = ⊥-elim (d refl)
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | yes p | no q
  with name₁ ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | yes p | no q | yes z = refl
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | yes p | no q | no z  = ⊥-elim (z refl)
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p | yes q
  rewrite q with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | yes z
  rewrite z = ⊥-elim (p refl)
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | yes s = ⊥-elim (z s)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s
  with name₁ ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | yes y
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | yes y | yes k = ⊥-elim (s k)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | yes y | no k = e
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | no y = ⊥-elim (y refl)
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s
  with name₁ ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | yes y
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | yes y | yes k = ⊥-elim (s k)
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | yes y | no k = e
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | yes q | no z | no s | no y = ⊥-elim (y refl)
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p | no q
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ ∷ w} {name} {r} {just v} name' v' d e | no p | no q | yes z
  rewrite z = ⊥-elim (p refl)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z
  with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | yes y = ⊥-elim (q y)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | no y
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | no y | yes s = ⊥-elim (p s)
getRef-update-¬≡ {cell name₁ r₁ nothing ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | no y | no s =
  getRef-update-¬≡ {w} name' v' d e
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z
  with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | yes y = ⊥-elim (q y)
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | no y
  with name ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | no y | yes s = ⊥-elim (p s)
getRef-update-¬≡ {cell name₁ r₁ (just v₁) ∷ w} {name} {r} {just v} name' v' d e | no p | no q | no z | no y | no s =
  getRef-update-¬≡ {w} name' v' d e


¬∈wdom→getRef-nothing : {n : Name} {w : 𝕎·}
                      → ¬ n ∈ wdom w
                      → getRef n w ≡ nothing
¬∈wdom→getRef-nothing {n} {[]} ni = refl
¬∈wdom→getRef-nothing {n} {cell name r v ∷ w} ni with n ≟ name
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = ¬∈wdom→getRef-nothing {n} {w} (λ x → ni (there x))


{--
→Rfrz? : {r : Res{0ℓ}} → Res.frz r ≡ true → Rfrz? r
→Rfrz? {r} e rewrite e = tt


Rfrz?→ : {r : Res{0ℓ}} → Rfrz? r → Res.frz r ≡ true
Rfrz?→ {r} e with Res.frz r
... | true = refl
... | false = ⊥-elim e


→¬Rfrz? : {r : Res{0ℓ}} → Res.frz r ≡ false → ¬ Rfrz? r
→¬Rfrz? {r} e rewrite e = λ z → z
--}


⊑-pres-getRef : {w1 w2 : world} {name : Name} {r : Res} {v : Mℂ·}
              → w1 ⊑· w2
              → getRef name w1 ≡ just (cell name r v)
              → Σ Mℂ· (λ v' →
                getRef name w2 ≡ just (cell name r v')
                × pres-resSatRef v v' r
                × satFrozen r v v')
⊑-pres-getRef {w1} {.w1} {name} {r} {v} (≼-refl .w1) i =
  v , i , pres-resSatRef-refl v r , satFrozen-refl r v
⊑-pres-getRef {w1} {w3} {name} {r} {v} (≼-trans {.w1} {w2} {.w3} e₁ e₂) i
  with ⊑-pres-getRef {w1} {w2} {name} {r} {v} e₁ i
... | v' , i' , p' , s'
  with ⊑-pres-getRef {w2} {w3} {name} {r} {v'} e₂ i'
... | v'' , i'' , p'' , s'' = v'' , i'' , pres-resSatRef-trans p' p'' , satFrozen-trans {r = r} s' s''
⊑-pres-getRef {w1} {.(update n v₁ w1)} {name} {r} {v} (upd .w1 n r₁ v₁ hr x) i with n ≟ name
⊑-pres-getRef {w1} {.(update n v₁ w1)} {name} {r} {nothing} (upd .w1 n r₁ v₁ (mx , hr) x) i | yes p
  rewrite p | cell-inj2 (just-inj (trans (sym hr) i))
  = just v₁ , getRef-update-nothing-≡ {w1} {name} {r} {v₁} i , (λ _ → x) , tt
⊑-pres-getRef {w1} {.(update n v₁ w1)} {name} {r} {just v} (upd .w1 n r₁ v₁ hr x) i | yes p
  rewrite p
  = just v , getRef-update-just-≡ {w1} {name} {r} {v} v₁ i , (λ x → x) , refl
⊑-pres-getRef {w1} {.(update n v₁ w1)} {name} {r} {v} (upd .w1 n r₁ v₁ hr x) i | no p =
  v , getRef-update-¬≡ {w1} {name} {r} {v} n v₁ p i , (λ x → x) , satFrozen-refl r v
⊑-pres-getRef {w1} {.(cell n r₁ nothing ∷ w1)} {name} {r} {v} (new .w1 n r₁ x) i with name ≟ n
... | yes p rewrite p | ¬∈wdom→getRef-nothing {n} {w1} x = ⊥-elim (¬just≡nothing (sym i))
... | no p = v , i , (λ x → x) , satFrozen-refl r v


⊑-compatibleRef : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatibleRef c w1 r → compatibleRef c w2 r
⊑-compatibleRef {c} {w1} {w2} {r} e (v , comp , sat)
  with ⊑-pres-getRef {w1} {w2} {c} {r} {v} e comp
... | v' , i' , pr , sf = v' , i' , pr sat


open import compatible(PossibleWorldsRef)(choiceRef)

compatibleREF : Compatible
compatibleREF = mkCompatible compatibleRef ⊑-compatibleRef

open import compatibleDef(PossibleWorldsRef)(choiceRef)(compatibleREF)


getRefChoice : (n : ℕ) (name : Name) (w : world) → Maybe ℂ·
getRefChoice _ name w with getRef name w
... | just (cell _ _ v) = v
... | nothing = nothing


getRefChoiceCompatible : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) (n : ℕ) (t : ℂ·)
                       → compatibleRef c w r → getRefChoice n c w ≡ just t → ·ᵣ r n t
getRefChoiceCompatible c r w n t (k , i , sat) g
  rewrite i | g = sat n


-- We're really only generating numbers as choices here
T→ℂref : Term → ℂ·
T→ℂref (INL AX) = true
T→ℂref (INR AX) = false
T→ℂref _ = true


getRef⊎ : (name : Name) (w : world)
        → Σ Cell (λ c → getRef name w ≡ just c)
        ⊎ getRef name w ≡ nothing
getRef⊎ name w with getRef name w
... | just c = inj₁ (c , refl)
... | nothing = inj₂ refl


chooseREF : (cs : Name) (w : 𝕎·) (c : ℂ·) → 𝕎·
chooseREF n w c with getRef⊎ n w
... | inj₁ (cell name r v , e) with Res.dec r
... |    (true , D) with Res.inv r
... |       (true , I) with D 0 c
... |          inj₁ y = update n c w
... |          inj₂ y = w
chooseREF n w c | inj₁ (cell name r v , e) | (true , _) | (false , _) = w
chooseREF n w c | inj₁ (cell name r v , e) | (false , _) = w
chooseREF n w c | inj₂ _ = w


getRef→∈world : {n name : Name} {w : 𝕎·} {r : Res} {v : Mℂ·}
              → getRef n w ≡ just (cell name r v)
              → ∈world n r v w
getRef→∈world {n} {name} {cell name₁ r₁ v₁ ∷ w} {r} {v} h with n ≟ name₁
... | yes p rewrite p | h | cell-inj1 (just-inj h) = refl
... | no p = getRef→∈world {n} {name} {w} h


chooseREF⊑ : (cs : Name) (w : 𝕎·) (c : ℂ·) → w ⊑· chooseREF cs w c
chooseREF⊑ n w c with getRef⊎ n w
... | inj₁ (cell name r v , e) with Res.dec r
... |    (true , D) with Res.inv r
... |       (true , I) with D 0 c
... |          inj₁ y = upd w n r c (v , getRef→∈world {n} {name} {w} e) (inv→·ᵣ→⋆ᵣ {r} {c} I y)
... |          inj₂ y = ⊑-refl· _
chooseREF⊑ n w c | inj₁ (cell name r v , e) | (true , _) | (false , _) = ⊑-refl· _
chooseREF⊑ n w c | inj₁ (cell name r v , e) | (false , _) = ⊑-refl· _
chooseREF⊑ n w c | inj₂ _ = ⊑-refl· _


isℂ₀ref : ℂ· → Bool
isℂ₀ref b = b


open import getChoice(PossibleWorldsRef)(choiceRef)(compatibleREF)

getChoiceRef : GetChoice
getChoiceRef = mkGetChoice getRefChoice T→ℂref chooseREF chooseREF⊑
-- wdom
-- isℂ₀ref
-- getRefChoiceCompatible

open import getChoiceDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)


progressRef : (c : Name) (w1 w2 : 𝕎·) → Set₁
progressRef c w1 w2 =
  (r : Res) (v : Mℂ·)
  → ∈world c r v w1
  → Σ ℂ· (λ v' → ∈world c r (just v') w2 × satFrozen r v (just v'))


progRef : (c : Name) (w1 w2 : 𝕎·) → Set₁
progRef c w1 w2 =
  (r : Res) (v : Mℂ·)
  → ∈world c r v w1
  → Σ Mℂ· (λ v' → ∈world c r v' w2 × satFrozen r v v')


progressRef-trans : {c : Name} {w1 w2 w3 : 𝕎·}
                  → progressRef c w1 w2
                  → progressRef c w2 w3
                  → progressRef c w1 w3
progressRef-trans {c} {w1} {w2} {w3} p1 p2 r v i
  with p1 r v i
... | v' , i' , sf'
  with p2 r (just v') i'
... | v'' , i'' , sf'' =
  v'' , i'' , satFrozen-trans {r = r} sf' sf''


freezeDef : NRes{0ℓ} → 𝕎· → 𝕎·
freezeDef r w = update (NRes.name r) (Res.c₀ (NRes.res r)) w


freezeList : List (NRes{0ℓ}) → 𝕎· → 𝕎·
freezeList [] w = w
freezeList (r ∷ l) w = freezeDef r (freezeList l w)


freezeSeq : List NRes → 𝕎· → ℕ → 𝕎·
freezeSeq l w 0 = w
freezeSeq l w (suc n) = freezeList l (freezeSeq l w n)


𝕎→seq : 𝕎· → ℕ → 𝕎·
𝕎→seq w = freezeSeq (wrdom w) w


⊑𝕎→seq0 : (w : 𝕎·) → w ⊑· 𝕎→seq w 0
⊑𝕎→seq0 w = ⊑-refl· w


compatibleNRes : (r : NRes) (w : 𝕎·) → Set₁
compatibleNRes r w = hasRes (NRes.name r) w (NRes.res r)


⊑→compatibleNRes : {r : NRes} {w1 w2 : 𝕎·} → w1 ⊑· w2 → compatibleNRes r w1 → compatibleNRes r w2
⊑→compatibleNRes {r} {w1} {w2} e (v , comp)
  with ⊑-pres-getRef {w1} {w2} {NRes.name r} {NRes.res r} {v} e comp
... | v' , g' , s' , f' = v' , g'


compatibleListNRes : (l : List NRes) (w : 𝕎·) → Set₁
compatibleListNRes l w = (r : NRes) → r ∈ l → compatibleNRes r w


⊑→compatibleListNRes : {k : List NRes} {w1 w2 : 𝕎·} → w1 ⊑· w2 → compatibleListNRes k w1 → compatibleListNRes k w2
⊑→compatibleListNRes {k} {w1} {w2} e comp r i = ⊑→compatibleNRes e (comp r i)


--getRef→∈world : {c : Name} {r : Res} {w : 𝕎·} {v : Mℂ·} → getRef c w ≡ just (cell c r v) → ∈world c r v w
--getRef→∈world {c} {r} {w} {l} h rewrite h = refl


¬∈remNRes : {L : Level} {r : NRes{L}} {l : List (NRes{L})}
              → ¬ r ∈ (remNRes (NRes.name r) l)
¬∈remNRes {L} {r} {x ∷ l} i with NRes.name r ≟ NRes.name x
... | yes p = ¬∈remNRes {L} {r} {l} i
¬∈remNRes {L} {r} {x ∷ l} (here px) | no p rewrite px = ⊥-elim (p refl)
¬∈remNRes {L} {r} {x ∷ l} (there i) | no p = ¬∈remNRes {L} {r} {l} i


∈∷remNRes→ : {L : Level} {r : NRes{L}} {res : Res{L}} {l : List (NRes{L})}
              → r ∈ (mkNRes (NRes.name r) res ∷ remNRes (NRes.name r) l)
              → res ≡ NRes.res r
∈∷remNRes→ {L} {r} {res} {l} (here px) rewrite px = refl
∈∷remNRes→ {L} {r} {res} {l} (there i) = ⊥-elim (¬∈remNRes {L} {r} {l} i)


∈remNRes→ : {L : Level} (name : Name) {r : NRes{L}} {l : List (NRes{L})} → r ∈ remNRes name l → r ∈ l
∈remNRes→ {L} name {r} {x ∷ l} i with name ≟ NRes.name x
... | yes p rewrite p = there (∈remNRes→ (NRes.name x) i)
∈remNRes→ {L} name {r} {x ∷ l} (here px) | no p rewrite px = here refl
∈remNRes→ {L} name {r} {x ∷ l} (there i) | no p = there (∈remNRes→ name i)


∈wdom→∈world : {r : NRes} {w : 𝕎·} → r ∈ wrdom w → Σ Mℂ· (λ v → ∈world (NRes.name r) (NRes.res r) v w)
∈wdom→∈world {r} {cell name r₁ v ∷ w} i with NRes.name r ≟ name
∈wdom→∈world {r} {cell name r₁ v ∷ w} (here px) | yes p
  rewrite px
  = v , refl
∈wdom→∈world {r} {cell name r₁ v ∷ w} (there i) | yes p
  rewrite sym p
  = ⊥-elim (¬∈remNRes {r = r} {l = wrdom w} i)
∈wdom→∈world {r} {cell name r₁ v ∷ w} (here px) | no p
  rewrite px
  = ⊥-elim (p refl)
∈wdom→∈world {r} {cell name r₁ v ∷ w} (there i) | no p
  = ∈wdom→∈world {r} {w} (∈remNRes→ name i)


compatibleListNRes-wrdom : (w : 𝕎·) → compatibleListNRes (wrdom w) w
compatibleListNRes-wrdom w r i = ∈wdom→∈world {r} {w} i


⊑freezeDef : (r : NRes) (w : 𝕎·) → compatibleNRes r w → w ⊑· freezeDef r w
⊑freezeDef r w comp = upd w (NRes.name r) (NRes.res r) (Res.c₀ (NRes.res r)) comp (Res.sat₀ (NRes.res r))


⊑freezeList : (w : 𝕎·) (l : List NRes) → compatibleListNRes l w → w ⊑· freezeList l w
⊑freezeList w [] comp = ⊑-refl· w
⊑freezeList w (x ∷ l) comp = ⊑-trans· (⊑freezeList w l comp1) (⊑freezeDef x (freezeList l w) comp2)
  where
    comp0 : compatibleNRes x w
    comp0 = comp x (here refl)

    comp1 : compatibleListNRes l w
    comp1 r i = comp r (there i)

    comp2 : compatibleNRes x (freezeList l w)
    comp2 = ⊑→compatibleNRes (⊑freezeList w l comp1) comp0


⊑freezeSeq : {l : List NRes} {w : 𝕎·} (n : ℕ) → compatibleListNRes l w → w ⊑· freezeSeq l w n
⊑freezeSeq {l} {w} 0 comp = ⊑-refl· w
⊑freezeSeq {l} {w} (suc n) comp =
  ⊑-trans· (⊑freezeSeq n comp)
           (⊑freezeList (freezeSeq l w n) l (⊑→compatibleListNRes (⊑freezeSeq n comp) comp))


⊑𝕎→seqS : (w : 𝕎·) (n : ℕ) → 𝕎→seq w n ⊑· 𝕎→seq w (suc n)
⊑𝕎→seqS w n = ⊑freezeList (𝕎→seq w n)
                            (wrdom w)
                            (⊑→compatibleListNRes (⊑freezeSeq n (compatibleListNRes-wrdom w)) (compatibleListNRes-wrdom w))


𝕎→refChain : (w : 𝕎·) → chain w
𝕎→refChain w =
  mkChain
    (𝕎→seq w)
    (⊑𝕎→seq0 w)
    (⊑𝕎→seqS w)


{--
progressRef-refl : (c : Name) (w : 𝕎·) → progressRef c w w
progressRef-refl c w r v i = {!!} --just v , i , satFrozen-refl r v
--}


→∈remNRes : {L : Level} (name : Name) {r : NRes{L}} {l : List (NRes{L})} → ¬ NRes.name r ≡ name  → r ∈ l → r ∈ remNRes name l
→∈remNRes {L} name {r} {x ∷ l} d (here px) with name ≟ NRes.name x
... | yes p rewrite px | p = ⊥-elim (d refl)
... | no p rewrite px = here refl
→∈remNRes {L} name {r} {x ∷ l} d (there i) with name ≟ NRes.name x
... | yes p rewrite p = →∈remNRes (NRes.name x) d i
... | no p = there (→∈remNRes name d i)


getRef→mkNRes∈wrdom : {c : Name} {w : 𝕎·} {v : Mℂ·} {r : Res}
                      → getRef c w ≡ just (cell c r v)
                      → mkNRes c r ∈ wrdom w
getRef→mkNRes∈wrdom {c} {cell name r₁ v ∷ w} {l} {r} e
  with c ≟ name
getRef→mkNRes∈wrdom {c} {cell name r₁ v ∷ w} {l} {r} e | yes p
  rewrite cell-inj1 (just-inj e) | cell-inj2 (just-inj e) | cell-inj3 (just-inj e)
  = here refl
getRef→mkNRes∈wrdom {c} {cell name r₁ v ∷ w} {l} {r} e | no p =
  there (→∈remNRes name p (getRef→mkNRes∈wrdom {c} {w} {l} {r} e))


wrdom-freezeDef : (w : 𝕎·) (x : NRes) → wrdom (freezeDef x w) ≡ wrdom w
wrdom-freezeDef [] x = refl
wrdom-freezeDef (cell name res nothing ∷ w) x
  rewrite wrdom-freezeDef w x
  with NRes.name x ≟ name
wrdom-freezeDef (cell name res nothing ∷ w) x | yes p = refl
wrdom-freezeDef (cell name res nothing ∷ w) x | no p
  rewrite wrdom-freezeDef w x
  = refl
wrdom-freezeDef (cell name res (just v) ∷ w) x
  rewrite wrdom-freezeDef w x
  with NRes.name x ≟ name
wrdom-freezeDef (cell name res (just v) ∷ w)  x | yes p = refl --refl
wrdom-freezeDef (cell name res (just v) ∷ w)  x | no p
  rewrite wrdom-freezeDef w x
  = refl


wrdom-freezeList : (w : 𝕎·) (l : List NRes) → wrdom (freezeList l w) ≡ wrdom w
wrdom-freezeList w [] = refl
wrdom-freezeList w (x ∷ l) rewrite wrdom-freezeDef (freezeList l w) x = wrdom-freezeList w l


wrdom-freezeSeq : (w : 𝕎·) (l : List NRes) (n : ℕ) → wrdom (freezeSeq l w n) ≡ wrdom w
wrdom-freezeSeq w l 0 = refl
wrdom-freezeSeq w l (suc n) rewrite wrdom-freezeList (freezeSeq l w n) l = wrdom-freezeSeq w l n


∈wrdom-freezeSeq→ : (r : NRes) (l : List NRes) (w : 𝕎·) (n : ℕ)
                     → r ∈ wrdom (freezeSeq l w n)
                     → r ∈ wrdom w
∈wrdom-freezeSeq→ r l w n i rewrite wrdom-freezeSeq w l n  = i


NRes-nodup : {L : Level} (l : List (NRes{L})) → Set
NRes-nodup {L} [] = ⊤
NRes-nodup {L} (r ∷ l) = ¬ (NRes.name r ∈ Data.List.map NRes.name l) × NRes-nodup l


¬≡→≡getRef-update : (c name : Name) (w : 𝕎·) (t : ℂ·)
                   → ¬ c ≡ name
                   → getRef c (update name t w) ≡ getRef c w
¬≡→≡getRef-update c name [] t d = refl
¬≡→≡getRef-update c name (cell name₁ r v ∷ w) t d
  with c ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | yes p
  rewrite p
  with name ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | yes p | yes q = ⊥-elim (d (sym q))
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | yes p | no q
  with name₁ ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | yes p | no q | yes z = refl
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | yes p | no q | no z = ⊥-elim (z refl)
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | yes p
  rewrite p
  with name ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | yes p | yes q = ⊥-elim (d (sym q))
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | yes p | no q
  with name₁ ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | yes p | no q | yes z = refl
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | yes p | no q | no z = ⊥-elim (z refl)
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p
  with name ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p | yes q
  rewrite q
  with c ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p | yes q | yes z = ⊥-elim (p z)
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p | yes q | no z = refl
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p | no q
  with c ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p | no q | yes z = ⊥-elim (p z)
¬≡→≡getRef-update c name (cell name₁ r nothing ∷ w) t d | no p | no q | no z =
  ¬≡→≡getRef-update c name w t d
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p
  with name ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p | yes q
  rewrite q
  with c ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p | yes q | yes z = ⊥-elim (d z)
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p | yes q | no z = refl
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p | no q
  with c ≟ name₁
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p | no q | yes z = ⊥-elim (p z)
¬≡→≡getRef-update c name (cell name₁ r (just v) ∷ w) t d | no p | no q | no z =
  ¬≡→≡getRef-update c name w t d


¬∈→getRef-freezeList : {c : Name} {k : List NRes} {w : 𝕎·} {e : Cell}
                     → ¬ c ∈ Data.List.map NRes.name k
                     → getRef c w ≡ just e
                     → getRef c (freezeList k w) ≡ just e
¬∈→getRef-freezeList {c} {[]} {w} {e} ni z = z
¬∈→getRef-freezeList {c} {x ∷ k} {w} {e} ni z
  rewrite ¬≡→≡getRef-update c (NRes.name x) (freezeList k w) (Res.c₀ (NRes.res x)) (λ x → ni (here x))
  = ¬∈→getRef-freezeList (λ x → ni (there x)) z


getRef-freezeList≡-aux : {L : Level} {c name : Name} {k : List (NRes{L})} {r : Res{L}}
                        → c ≡ name
                        → mkNRes c r ∈ k
                        → name ∈ Data.List.map NRes.name k
getRef-freezeList≡-aux {L} {c} {name} {x ∷ k} {r} e (here px) rewrite e | sym px = here refl
getRef-freezeList≡-aux {L} {c} {name} {x ∷ k} {r} e (there i) = there (getRef-freezeList≡-aux e i)


getRef-freezeList≡-nothing : {c : Name} {r : Res} {k : List NRes} {w : 𝕎·}
                          → NRes-nodup k
                          → mkNRes c r ∈ k
                          → getRef c w ≡ just (cell c r nothing)
                          → getRef c (freezeList k w) ≡ just (cell c r (just (Res.c₀ r)))
getRef-freezeList≡-nothing {c} {r} {x ∷ k} {w} (d , nd) (here px) e rewrite sym px =
  getRef-update-nothing-≡ {freezeList k w} {c} {r} {Res.c₀ r} z1
  where
  z1 : getRef c (freezeList k w) ≡ just (cell c r nothing)
  z1 = ¬∈→getRef-freezeList d e
getRef-freezeList≡-nothing {c} {r} {x ∷ k} {w} (d , nd) (there i) e =
  getRef-update-¬≡ {freezeList k w} {c} {r} {just (Res.c₀ r)} (NRes.name x) (Res.c₀ (NRes.res x)) d' z1
  where
  z1 : getRef c (freezeList k w) ≡ just (cell c r (just (Res.c₀ r)))
  z1 = getRef-freezeList≡-nothing {c} {r} {k} {w} nd i e

  d' : ¬ NRes.name x ≡ c
  d' y rewrite sym y = d (getRef-freezeList≡-aux (sym y) i)


getRef-freezeList≡-just : {c : Name} {r : Res} {k : List NRes} {w : 𝕎·} {v : ℂ·}
                        → getRef c w ≡ just (cell c r (just v))
                        → getRef c (freezeList k w) ≡ just (cell c r (just v))
getRef-freezeList≡-just {c} {r} {[]} {w} {v} e = e
getRef-freezeList≡-just {c} {r} {mkNRes n r' ∷ k} {w} {v} e =
  getRef-update-just-≡' {freezeList k w} {c} {n} {r} {v} (Res.c₀ r') i1
  where
  i1 : getRef c (freezeList k w) ≡ just (cell c r (just v))
  i1 = getRef-freezeList≡-just {c} {r} {k} {w} {v} e

{--
 rewrite sym px =
  getRef-update-nothing-≡ {freezeList k w} {c} {r} {Res.c₀ r} z1
  where
  z1 : getRef c (freezeList k w) ≡ just (cell c r nothing)
  z1 = ¬∈→getRef-freezeList d e
getRef-freezeList≡-just {c} {r} {x ∷ k} {w} {v} (d , nd) (there i) e =
  getRef-update-¬≡ {freezeList k w} {c} {r} {just (Res.c₀ r)} (NRes.name x) (Res.c₀ (NRes.res x)) d' z1
  where
  z1 : getRef c (freezeList k w) ≡ just (cell c r (just (Res.c₀ r)))
  z1 = getRef-freezeList≡-nothing {c} {r} {k} {w} nd i e

  d' : ¬ NRes.name x ≡ c
  d' y rewrite sym y = d (getRef-freezeList≡-aux (sym y) i)
--}


¬∈map-remNRes : {L : Level} (name : Name) (l : List (NRes{L})) → ¬ name ∈ Data.List.map NRes.name (remNRes name l)
¬∈map-remNRes {L} name (x ∷ l) i with name ≟ NRes.name x
... | yes p = ¬∈map-remNRes name l i
¬∈map-remNRes {L} name (x ∷ l) (here px) | no p = p px
¬∈map-remNRes {L} name (x ∷ l) (there i) | no p = ¬∈map-remNRes name l i


∈map-remNRes→ : {L : Level} {name x : Name} {l : List (NRes{L})}
                 → x ∈ Data.List.map NRes.name (remNRes name l)
                 → x ∈ Data.List.map NRes.name l
∈map-remNRes→ {L} {name} {x} {x₁ ∷ l} i with name ≟ NRes.name x₁
... | yes p = there (∈map-remNRes→ i)
∈map-remNRes→ {L} {name} {x} {x₁ ∷ l} (here px) | no p = here px
∈map-remNRes→ {L} {name} {x} {x₁ ∷ l} (there i) | no p = there (∈map-remNRes→ i)


→NRes-nodup-remNRes : {L : Level} (name : Name) (l : List (NRes{L})) → NRes-nodup l → NRes-nodup (remNRes name l)
→NRes-nodup-remNRes {L} name [] nd = nd
→NRes-nodup-remNRes {L} name (x ∷ l) (d , nd) with name ≟ NRes.name x
... | yes p rewrite p = →NRes-nodup-remNRes (NRes.name x) l nd
... | no p = (λ i → d (∈map-remNRes→ i)) , →NRes-nodup-remNRes name l nd


NRes-nodup-wdom : (w : 𝕎·) → NRes-nodup (wrdom w)
NRes-nodup-wdom [] = tt
NRes-nodup-wdom (cell c r v ∷ w) = ¬∈map-remNRes c (wrdom w) , →NRes-nodup-remNRes c (wrdom w) (NRes-nodup-wdom w)


refChainProgress : (w : 𝕎·) (x : Name) (n : ℕ) {r : Res{0ℓ}}
                 → compatibleRef x (chain.seq (𝕎→refChain w) n) r
                 → Σ ℕ (λ m → n < m × progressRef x (chain.seq (𝕎→refChain w) n) (chain.seq (𝕎→refChain w) m))
refChainProgress w x n {r} (v , i , sat) = suc n , ≤-refl , p --progressRef-refl x w
  where
  p : progressRef x (chain.seq (𝕎→refChain w) n) (chain.seq (𝕎→refChain w) (suc n))
  p r' nothing i' rewrite i | sym (cell-inj2 (just-inj i')) | cell-inj3 (just-inj i') =
    Res.c₀  r' , i3 , tt
    where
    i1 : mkNRes x r ∈ wrdom (freezeSeq (wrdom w) w n)
    i1 = getRef→mkNRes∈wrdom {x} {freezeSeq (wrdom w) w n} i

    i2 : mkNRes x r ∈ wrdom w
    i2 = ∈wrdom-freezeSeq→ (mkNRes x r) (wrdom w) w n i1

    i3 : getRef x (freezeList (wrdom w) (freezeSeq (wrdom w) w n)) ≡ just (cell x r (just (Res.c₀ r')))
    i3 rewrite sym (cell-inj2 (just-inj i')) =
      getRef-freezeList≡-nothing {x} {r} {wrdom w}{freezeSeq (wrdom w) w n} (NRes-nodup-wdom w) i2 i
  p r' (just v') i' rewrite i | sym (cell-inj2 (just-inj i')) | cell-inj3 (just-inj i') =
    v' , i3 , refl
    where
    i1 : mkNRes x r ∈ wrdom (freezeSeq (wrdom w) w n)
    i1 = getRef→mkNRes∈wrdom {x} {freezeSeq (wrdom w) w n} i

    i2 : mkNRes x r ∈ wrdom w
    i2 = ∈wrdom-freezeSeq→ (mkNRes x r) (wrdom w) w n i1

    i3 : getRef x (freezeList (wrdom w) (freezeSeq (wrdom w) w n)) ≡ just (cell x r (just v'))
    i3 rewrite sym (cell-inj2 (just-inj i')) =
      getRef-freezeList≡-just {x} {r} {wrdom w} {freezeSeq (wrdom w) w n} {v'} i


open import progress(PossibleWorldsRef)(choiceRef)(compatibleREF)

progressREF : Progress
progressREF =
  mkProgress
    progressRef
    𝕎→refChain
    refChainProgress

open import progressDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)


C0 : ℂ·
C0 = true --0


C1 : ℂ·
C1 = false --1


decℂ₀ref : (c : ℂ·) → c ≡ C0 ⊎ ¬ c ≡ C0
decℂ₀ref false = inj₂ (λ ())
decℂ₀ref true = inj₁ refl


decℂ₁ref : (c : ℂ·) → c ≡ C1 ⊎ ¬ c ≡ C1
decℂ₁ref false = inj₁ refl
decℂ₁ref true = inj₂ (λ ())


open import choiceExt{1ℓ}(PossibleWorldsRef)(choiceRef)

choiceExtRef : ChoiceExt
choiceExtRef = mkChoiceExt C0 C1 decℂ₀ref decℂ₁ref

open import choiceExtDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(choiceExtRef)


newRefChoice : (w : 𝕎·) → Name
newRefChoice w = fst (freshName (wdom w ++ wnames w))


startRefChoice : (n : Name) (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
startRefChoice n r w = newCell n r w


startNewRefChoice : (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
startNewRefChoice r w = startRefChoice (newRefChoice w) r w


getRef-newCell : (w : 𝕎·) (name : Name) (r : Res)
               → getRef name (newCell name r w) ≡ just (cell name r nothing)
getRef-newCell w name r with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)


getRefChoice-startRefChoice : (n : ℕ) (r : Res) (w : 𝕎·) (t : ℂ·) (name : Name)
                            → ¬ name ∈ wdom w
                            → getRefChoice n name (startRefChoice name r w) ≡ just t → t ≡ Res.c₀ r
--                             → getRefChoice n (newRefChoice w) (startNewRefChoice r w) ≡ nothing
getRefChoice-startRefChoice n r w t name ni e
  rewrite getRef-newCell w name r
  = ⊥-elim (¬just≡nothing (sym e))


startRefChoice⊏ : (r : Res) (w : 𝕎·) (name : Name) → ¬ name ∈ wdom w → w ⊑· startRefChoice name r w
startRefChoice⊏ r w name ni = new w name r ni


startRefChoiceCompatible : (r : Res{0ℓ}) (w : 𝕎·) (name : Name)
                         → ¬ name ∈ wdom w → compatibleRef name (startRefChoice name r w) r
startRefChoiceCompatible r w name ni =
  nothing , getRef-newCell w name r , tt


open import newChoice(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)

newChoiceRef : NewChoice
newChoiceRef =
  mkNewChoice
    wdom --newRefChoice
    wnames
    startRefChoice
    getRefChoice-startRefChoice
    startRefChoice⊏
    startRefChoiceCompatible

open import newChoiceDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(newChoiceRef)


open import encoding3(E)


open import computation(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(choiceExtRef)(newChoiceRef)(enc)


¬∼c01 : (w : 𝕎·) → ¬ ∼C! w (ℂ→C· C0) (ℂ→C· C1)
¬∼c01 w h = x (#compVal (∼C!→#⇓ {w} {ℂ→C· C0} {ℂ→C· C1} tt h) tt)
  where
    x : ℂ→C· C0 ≡ ℂ→C· C1 → ⊥
    x ()


ℂ→T→ℂ0 : T→ℂ· ⌜ Cℂ₀ ⌝ ≡ ℂ₀·
ℂ→T→ℂ0 = refl


ℂ→T→ℂ1 : T→ℂ· ⌜ Cℂ₁ ⌝ ≡ ℂ₁·
ℂ→T→ℂ1 = refl


open import choiceVal{1ℓ}(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(choiceExtRef)(newChoiceRef)(enc)

choiceValRef : ChoiceVal
choiceValRef = mkChoiceVal ¬∼c01 tt tt ℂ→T→ℂ0 ℂ→T→ℂ1

open import choiceValDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)(choiceExtRef)(newChoiceRef)(enc)(choiceValRef)


freezeRef : (n : Name) (w : 𝕎·) (v : ℂ·) → world
freezeRef n w v = update n v w


hasRes∷ : (name : Name) (r : Res) (v : Mℂ·) (w : 𝕎·)
        → hasRes name (cell name r v ∷ w) r
hasRes∷ name r v w with name ≟ name
... | yes p = v , refl
... | no p = ⊥-elim (p refl)


freezableRef : (c : Name) (w : 𝕎·) → Set
freezableRef c w with getRef c w
... | just (cell n r nothing) = ⊤
... | _ = ⊥


{--
⊑-freeze∷ : (name : Name) (r : Res) (v₁ v₂ : ℂ·) (w : 𝕎·)
            → ⋆ᵣ r v₂
            → (cell name r v₁ false ∷ w) ⊑· (cell name r v₂ true ∷ w)
⊑-freeze∷ name r v₁ v₂ w sat =
  ⊑-trans· (upd (cell name r v₁ false ∷ w) name r v₂ true (hasRes∷ name r v₁ false w) sat) z
  where
    z : (update name v₂ true (cell name r v₁ false ∷ w)) ⊑· (cell name r v₂ true ∷ w)
    z with name ≟ name
    ... | yes p = ⊑-refl· _
    ... | no p = ⊥-elim (p refl)
--}


wdom++ : (w1 w2 : 𝕎·) → wdom (w1 ++ w2) ≡ wdom w1 ++ wdom w2
wdom++ [] w2 = refl
wdom++ (x ∷ w1) w2 rewrite wdom++ w1 w2 = refl


getRef++-¬∈ : {name : Name} (w1 w2 : 𝕎·)
              → ¬ name ∈ wdom w1
              → getRef name (w1 ++ w2) ≡ getRef name w2
getRef++-¬∈ {name} [] w2 ni = refl
getRef++-¬∈ {name} (cell name₁ r v ∷ w1) w2 ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = getRef++-¬∈ w1 w2 (λ x → ni (there x))


hasRes++-¬∈ : {name : Name} (w1 w2 : 𝕎·) (r : Res)
              → ¬ name ∈ wdom w1
              → hasRes name w2 r
              → hasRes name (w1 ++ w2) r
hasRes++-¬∈ {name} w1 w2 r ni hr rewrite getRef++-¬∈ w1 w2 ni = hr


update++-¬∈ : {name : Name} {w1 : 𝕎·} (w2 : 𝕎·) (t : ℂ·)
            → ¬ name ∈ wdom w1
            → update name t (w1 ++ w2) ≡ w1 ++ update name t w2
update++-¬∈ {name} {[]} w2 t ni = refl
update++-¬∈ {name} {cell name₁ r nothing ∷ w1} w2 t ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p rewrite update++-¬∈ {name} {w1} w2 t (λ x → ni (there x)) = refl
update++-¬∈ {name} {cell name₁ r (just v) ∷ w1} w2 t ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p rewrite update++-¬∈ {name} {w1} w2 t (λ x → ni (there x)) = refl


preFreezeRef⊑ : (c : Name) (w w' : 𝕎·) (t : ℂ·) {r : Res}
              → compatibleRef c w r
              → ⋆ᵣ r t
              → ¬ (c ∈ wdom w')
              → (w' ++ w) ⊑· (w' ++ freezeRef c w t)
preFreezeRef⊑ c (cell name r₁ nothing ∷ w) w' t {r} (v , comp , sat) rt ni
  with c ≟ name
preFreezeRef⊑ c (cell name r₁ nothing ∷ w) w' t {r} (v , comp , sat) rt ni | yes p
  rewrite p | sym (cell-inj2 (just-inj comp)) | sym (cell-inj3 (just-inj comp))
  = ⊑-trans· (upd (w' ++ cell name r₁ nothing ∷ w) name r₁ t hr' rt) e'
  where
  hr' : hasRes name (w' ++ cell name r₁ nothing ∷ w) r₁
  hr' = hasRes++-¬∈ w' (cell name r₁ nothing ∷ w) r₁ ni (hasRes∷ _ _ _ _)

  e' : update name t (w' ++ cell name r₁ nothing ∷ w) ⊑· (w' ++ cell name r₁ (just t) ∷ w)
  e' rewrite update++-¬∈ {name} {w'} (cell name r₁ nothing ∷ w) t ni with name ≟ name
  e' | yes x with t ≡ᵇ Res.c₁ r₁
  e' | yes x | inj₁ y = ⊑-refl· _
  e' | yes x | inj₂ y = ⊑-refl· _
  e' | no x = ⊥-elim (x refl)
preFreezeRef⊑ c (cell name r₁ nothing ∷ w) w' t {r} (v , comp , sat) rt ni | no p
  rewrite sym (++-assoc w' [ cell name r₁ nothing ] w)
        | sym (++-assoc w' [ cell name r₁ nothing ] (update c t w))
  = preFreezeRef⊑ c w (w' ++ [ cell name r₁ nothing ]) t {r} (v , comp , sat) rt ni'
  where
  ni' : ¬ c ∈ wdom (w' ++ [ cell name r₁ nothing ])
  ni' i rewrite wdom++ w' [ cell name r₁ nothing ] with ∈-++⁻ (wdom w') i
  ... | inj₁ q = ⊥-elim (ni q)
  ... | inj₂ (here q) = ⊥-elim (p q)
preFreezeRef⊑ c (cell name r₁ (just v₁) ∷ w) w' t {r} (v , comp , sat) rt ni
  with c ≟ name
preFreezeRef⊑ c (cell name r₁ (just v₁) ∷ w) w' t {r} (v , comp , sat) rt ni | yes p
  rewrite p = ≼-refl _
preFreezeRef⊑ c (cell name r₁ (just v₁) ∷ w) w' t {r} (v , comp , sat) rt ni | no p
  rewrite sym (++-assoc w' [ cell name r₁ (just v₁) ] w)
        | sym (++-assoc w' [ cell name r₁ (just v₁) ] (update c t w))
  = preFreezeRef⊑ c w (w' ++ [ cell name r₁ (just v₁) ]) t {r} (v , comp , sat) rt ni'
  where
  ni' : ¬ c ∈ wdom (w' ++ [ cell name r₁ (just v₁) ])
  ni' i rewrite wdom++ w' [ cell name r₁ (just v₁) ] with ∈-++⁻ (wdom w') i
  ... | inj₁ q = ⊥-elim (ni q)
  ... | inj₂ (here q) = ⊥-elim (p q)


freezeRef⊑ : (c : Name) (w : 𝕎·) {r : Res} → compatibleRef c w r → w ⊑· freezeRef c w (Res.c₁ r)
freezeRef⊑ c w {r} comp = preFreezeRef⊑ c w [] (Res.c₁ r) comp (Res.sat₁ r) λ ()


freezableStartRef : (r : Res{0ℓ}) (w : 𝕎·) → freezableRef (newRefChoice w) (startNewRefChoice r w)
freezableStartRef r w with newRefChoice w ≟ newRefChoice w
... | yes p = tt
... | no p = ⊥-elim (p refl)


progressFreeze : (r : Res) (c : Name) (w : 𝕎·) → Set₁
progressFreeze r c w =
    (v : Mℂ·)
  → ∈world c r v w
  → Σ ℂ· (λ v' → ∈world c r (just v') (freezeRef c w (Res.c₁ r)) × satFrozen r v (just v'))


progressRef-freeze : (c : Name) (w : 𝕎·) (r : Res) → progressFreeze r c w
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i
  with c ≟ name
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i | yes p
  rewrite p
  with name ≟ name
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i | yes p | yes q
  rewrite sym (cell-inj2 (just-inj i)) | sym (cell-inj3 (just-inj i))
  = Res.c₁ r₁ , refl , tt
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i | yes p | no q = ⊥-elim (q refl)
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i | no p
  with c ≟ name
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i | no p | yes q = ⊥-elim (p q)
progressRef-freeze c (cell name r₁ nothing ∷ w) r v i | no p | no q =
  progressRef-freeze c w r v i
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i
  with c ≟ name
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i | yes p
  rewrite p
  with name ≟ name
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i | yes p | yes q
  rewrite sym (cell-inj2 (just-inj i)) | sym (cell-inj3 (just-inj i))
  = v₁ , refl , refl
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i | yes p | no q = ⊥-elim (q refl)
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i | no p
  with c ≟ name
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i | no p | yes q = ⊥-elim (p q)
progressRef-freeze c (cell name r₁ (just v₁) ∷ w) r v i | no p | no q =
  progressRef-freeze c w r v i


⊑→progRef : (c : Name) {w1 w2 : 𝕎·} → w1 ⊑· w2 → progRef c w1 w2
⊑→progRef c {w1} {w2} e r v i
  with ⊑-pres-getRef e i
... | v' , i' , s' , f' = v' , i' , f'


getFreezeRef-aux : (c : Name) (w : 𝕎·) {r : Res{0ℓ}}
                 → compatibleRef c w r
                 → freezableRef c w
                 → Σ ℕ (λ n → ∀𝕎 (freezeRef c w (Res.c₁ r))
                                 (λ w' _ → Lift 2ℓ (getRefChoice n c w' ≡ just (Res.c₁ r) × ¬ freezableRef c w')))
getFreezeRef-aux c w {r} (just v , comp , sat) fb rewrite comp = ⊥-elim fb
getFreezeRef-aux c w {r} (nothing , comp , sat) fb rewrite comp = 0 , aw
  where
    t : ℂ·
    t = Res.c₁ r

    aw : ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (getRefChoice 0 c w' ≡ just t × ¬ freezableRef c w'))
    aw w1 e1 with progressRef-freeze c w r nothing comp
    ... | v1 , i1 , s1 with ⊑→progRef c e1 r (just v1) i1
    ... | nothing , i2 , s2 = ⊥-elim s2
    ... | just v2 , i2 , s2
      rewrite comp | s2 | i2
      rewrite getRef-update-nothing-≡ {w} {c} {r} {Res.c₁ r} comp
      rewrite sym (cell-inj3 (just-inj i1))
      = lift (refl , λ x → x)


getFreezeRef : (c : Name) (w : 𝕎·) {r : Res{0ℓ}}
             → compatibleRef c w r
             → Rfrz? r
             → freezableRef c w
             → Σ ℕ (λ n → ∀𝕎 (freezeRef c w (Res.c₁ r)) (λ w' _ → Lift 2ℓ (getRefChoice n c w' ≡ just (Res.c₁ r))))
getFreezeRef c w {r} comp frz fb
  with getFreezeRef-aux c w comp fb
... | n , F = n , λ w1 e1 → lift (fst (lower (F w1 e1)))


freezableRefDec : (c : Name) (w : 𝕎·) → freezableRef c w ⊎ ¬ freezableRef c w
freezableRefDec c w with getRef c w
... | just (cell n r nothing) = inj₁ tt
... | just (cell n r (just v)) = inj₂ (λ ())
... | nothing = inj₂ (λ ())


{--
¬freezableRef : (c : Name) (w : 𝕎·) {r : Res{0ℓ}}
              → compatible· c w r
              → Rfrz? r
              → ¬ freezableRef c w
              → Σ ℕ (λ n → ∀𝕎 w (λ w' _ → Lift 2ℓ (getChoice· n c w' ≡ just (Res.c₁ r))))
¬freezableRef c w {r} (v , true , i , rs , ft) frz nf
  rewrite i
  with ⊎bool (Res.frz r)
¬freezableRef c w {r} (v , true , i , rs , ft) frz nf | inj₁ p
  rewrite p
  with v ≡ᵇ Res.c₁ r
¬freezableRef c w {r} (v , true , i , rs , ft) frz nf | inj₁ p | inj₁ q
  rewrite q = 0 , h
  where
  h : (w' : List Cell) (e : w ≼ w') → Lift 2ℓ (getRefChoice 0 c w' ≡ just (Res.c₁ r))
  h w' e with ⊑-pres-getRef {w} {w'} {c} {r} {Res.c₁ r} {true} e i
  h w' e | v' , f' , gr , presr , satf , presf
    rewrite p | gr
    with Res.c₁ r ≡ᵇ Res.c₁ r
  ... | inj₁ z = lift (≡just (sym (snd (satf refl))))
  ... | inj₂ z = ⊥-elim (z refl)
¬freezableRef c w {r} (v , true , i , rs , ft) frz nf | inj₁ p | inj₂ q = ⊥-elim (true≠false (sym ft))
¬freezableRef c w {r} (v , true , i , rs , ft) frz nf | inj₂ p rewrite p = ⊥-elim frz
¬freezableRef c w {r} (v , false , i , rs , ft) frz nf
  rewrite i = ⊥-elim (nf tt)
--}


open import freeze(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(newChoiceRef)

freezeREF : Freeze
freezeREF =
  mkFreeze
    freezeRef
    freezableRef
    freezableRefDec
    freezeRef⊑
    getFreezeRef
    freezableStartRef
--    {!¬freezableRef!}

open import freezeDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(newChoiceRef)(freezeREF)

\end{code}
