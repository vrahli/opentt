\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import Function.Inverse using (Inverse)


open import util
open import calculus
open import world


module worldInstanceRef where
\end{code}



This provides an instance of world and choice for choice sequences


\begin{code}
-- The Bool says whether the cell is "frozen"
record Cell : Set₁ where
  constructor cell
  field
    name : Name
    r : Res{0ℓ}
    v : Term
    f : Bool


-- Worlds - entries are added at the end of the list
world : Set₁
world = List Cell


wdom : world → List Name
wdom [] = []
wdom (cell name _ _ _ ∷ w) = name ∷ wdom w


update : (n : Name) (v : Term) (f : Bool) (w : world) → world
update _ _ _ [] = []
update n v f (cell name r x b ∷ w) with n ≟ name
... | yes p = (if b then cell name r x b else cell name r v f) ∷ w
... | no p = cell name r x b ∷ update n v f w


newCell : (n : Name) (r : Res{0ℓ}) (w : world) → world
newCell n r w = cell n r (Res.def r) false ∷ w


getRef : Name → world → Maybe Cell
getRef name [] = nothing
getRef name (cell n r v f ∷ w) with name ≟ n
... | yes p = just (cell n r v f)
... | no p = getRef name w


∈world : (n : Name) (r : Res{0ℓ}) (v : Term) (f : Bool) (w : world) → Set₁
∈world n r v f w = getRef n w ≡ just (cell n r v f)


hasRes : (c : Name) (w : world) (r : Res{0ℓ}) → Set₁
hasRes c w r = Σ Term (λ v → Σ Bool (λ f → ∈world c r v f w))


data _≼_ : (w2 : world) (w1 : world) → Set₁ where
  ≼-refl : (w : world) → w ≼ w
  ≼-trans : {w1 w2 w3 : world} → w1 ≼ w2 → w2 ≼ w3 → w1 ≼ w3
  upd :
    (w : world) (n : Name) (r : Res{0ℓ}) (v : Term) (f : Bool)
    → hasRes n w r
    → ⋆ᵣ r v
    → w ≼ update n v f w
  new :
    (w : world) (n : Name) (r : Res{0ℓ})
    → ¬ (n ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → w ≼ newCell n r w


PossibleWorldsRef : PossibleWorlds
PossibleWorldsRef = mkPossibleWorlds world _≼_ ≼-refl ≼-trans


open import worldDef(PossibleWorldsRef)


open import choice(PossibleWorldsRef)


getRefChoice : (n : ℕ) (name : Name) (w : world) → Maybe Term
getRefChoice _ name w with getRef name w
... | just (cell _ _ v _) = just v
... | nothing = nothing


newRefChoice : (w : 𝕎·) → Name
newRefChoice w = fst (freshName (wdom w))


startRefChoice : (n : Name) (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
startRefChoice n r w = newCell n r w


startNewRefChoice : (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
startNewRefChoice r w = startRefChoice (newRefChoice w) r w


getRef-newCell : (w : 𝕎·) (name : Name) (r : Res)
                 → getRef name (newCell name r w) ≡ just (cell name r (Res.def r) false)
getRef-newCell w name r with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)


getRefChoice-startNewRefChoice : (n : ℕ) (r : Res) (w : 𝕎·) (t : Term)
                                 → getRefChoice n (newRefChoice w) (startNewRefChoice r w) ≡ just t → t ≡ Res.def r
--                                 → getRefChoice n (newRefChoice w) (startNewRefChoice r w) ≡ nothing
getRefChoice-startNewRefChoice n r w t e
  rewrite getRef-newCell w (newRefChoice w) r
        | just-inj e = refl


startNewRefChoice⊏ : (r : Res) (w : 𝕎·) → w ⊑· startNewRefChoice r w
startNewRefChoice⊏ r w = new w (newRefChoice w) r (snd (freshName (wdom w)))



resSatRef : (v : Term) (r : Res{0ℓ}) → Set
resSatRef v r = ⋆ᵣ r v


-- This is the same as 'hasRef' & enforces satisfiability too
compatibleRef : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set₁
compatibleRef c w r = Σ Term (λ v → Σ Bool (λ f → ∈world c r v f w × resSatRef v r))



pres-resSatRef : (v v' : Term) (r : Res{0ℓ}) → Set
pres-resSatRef v v' r = resSatRef v r → resSatRef v' r


pres-resSatRef-refl : (v : Term) (r : Res{0ℓ}) → pres-resSatRef v v r
pres-resSatRef-refl v r d = d


pres-resSatRef-trans : {v1 v2 v3 : Term} {r : Res{0ℓ}}
                       → pres-resSatRef v1 v2 r
                       → pres-resSatRef v2 v3 r
                       → pres-resSatRef v1 v3 r
pres-resSatRef-trans {v1} {v2} {v3} {r} p1 p2 s = p2 (p1 s)


cell-inj1 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Term} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → n1 ≡ n2
cell-inj1 refl =  refl


cell-inj2 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Term} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → r1 ≡ r2
cell-inj2 refl =  refl


cell-inj3 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Term} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → v1 ≡ v2
cell-inj3 refl =  refl


cell-inj4 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : Term} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → f1 ≡ f2
cell-inj4 refl =  refl


getRef-update-true-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : Term} (v' : Term) (f : Bool)
                     → getRef name w ≡ just (cell name r v true)
                     → getRef name (update name v' f w) ≡ just (cell name r v true)
getRef-update-true-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name₁ ≟ name₁
...     | yes q = refl
...     | no q = ⊥-elim (q refl)
getRef-update-true-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f e | no p with name ≟ name₁
...     | yes q = ⊥-elim (p q)
...     | no q = getRef-update-true-≡ {w} v' f e



getRef-update-false-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : Term} (v' : Term) (f : Bool)
                     → getRef name w ≡ just (cell name r v false)
                     → getRef name (update name v' f w) ≡ just (cell name r v' f)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name₁ ≟ name₁
...     | yes q = refl --refl
...     | no q = ⊥-elim (q refl)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f e | no p with name ≟ name₁
...     | yes q = ⊥-elim (p q)
...     | no q = getRef-update-false-≡ {w} v' f e



getRef-update-¬≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : Term} {f : Bool} (name' : Name) (v' : Term) (f' : Bool)
                     → ¬ name' ≡ name
                     → getRef name w ≡ just (cell name r v f)
                     → getRef name (update name' v' f' w) ≡ just (cell name r v f)
getRef-update-¬≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} {f} name' v' f' d e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name' ≟ name₁
... |    yes q rewrite q = ⊥-elim (d refl)
... |    no q with name₁ ≟ name₁
... |       yes z  = refl
... |       no z  = ⊥-elim (z refl)
getRef-update-¬≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} {f} name' v' f' d e | no p with name' ≟ name₁
getRef-update-¬≡ {cell name₁ r₁ v₁ true ∷ w} {name} {r} {v} {f} name' v' f' d e | no p | yes q rewrite q with name ≟ name₁
... |       yes z rewrite z = ⊥-elim (p refl)
... |       no z = e
getRef-update-¬≡ {cell name₁ r₁ v₁ false ∷ w} {name} {r} {v} {f} name' v' f' d e | no p | yes q rewrite q with name ≟ name₁
... |       yes z rewrite z = ⊥-elim (p refl)
... |       no z = e
getRef-update-¬≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} {f} name' v' f' d e | no p | no q with name ≟ name₁
... |       yes z rewrite z = ⊥-elim (p refl)
... |       no z = getRef-update-¬≡ {w} name' v' f' d e


¬∈wdom→getRef-nothing : {n : Name} {w : 𝕎·}
                         → ¬ n ∈ wdom w
                         → getRef n w ≡ nothing
¬∈wdom→getRef-nothing {n} {[]} ni = refl
¬∈wdom→getRef-nothing {n} {cell name r v f ∷ w} ni with n ≟ name
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = ¬∈wdom→getRef-nothing {n} {w} (λ x → ni (there x))


satFrozen : (v v' : Term) (f f' : Bool) → Set
satFrozen v v' true f' = f' ≡ true × v ≡ v'
satFrozen v v' false f' = ⊤


⊑-pres-getRef : {w1 w2 : world} {name : Name} {r : Res} {v : Term} {f : Bool}
                 → w1 ⊑· w2
                 → getRef name w1 ≡ just (cell name r v f)
                 → Σ Term (λ v' → Σ Bool (λ f' → getRef name w2 ≡ just (cell name r v' f') × pres-resSatRef v v' r))
⊑-pres-getRef {w1} {.w1} {name} {r} {v} {f} (≼-refl .w1) i = v , f , i , pres-resSatRef-refl v r
⊑-pres-getRef {w1} {w3} {name} {r} {v} {f} (≼-trans {.w1} {w2} {.w3} e₁ e₂) i =
  fst ind2 , fst (snd ind2) , fst (snd (snd ind2)) ,
  pres-resSatRef-trans {v} {fst ind1} {fst ind2} {r} (snd (snd (snd ind1))) (snd (snd (snd ind2)))
  where
    ind1 : Σ Term (λ v' → Σ Bool (λ f' → getRef name w2 ≡ just (cell name r v' f') × pres-resSatRef v v' r))
    ind1 = ⊑-pres-getRef e₁ i

    ind2 : Σ Term (λ v' → Σ Bool (λ f' → getRef name w3 ≡ just (cell name r v' f') × pres-resSatRef (fst ind1) v' r))
    ind2 = ⊑-pres-getRef e₂ (fst (snd (snd ind1)))
⊑-pres-getRef {w1} {.(update n v₁ f₁ w1)} {name} {r} {v} {true} (upd .w1 n r₁ v₁ f₁ hr x) i with n ≟ name
... | yes p rewrite p = v , true , (getRef-update-true-≡ {w1} v₁ f₁ i) , (λ x → x)
... | no p = v , true , getRef-update-¬≡ {w1} n v₁ f₁ p i , λ x → x
⊑-pres-getRef {w1} {.(update n v₁ f₁ w1)} {name} {r} {v} {false} (upd .w1 n r₁ v₁ f₁ hr x₁) i with n ≟ name
... | yes p rewrite p | i | sym (cell-inj2 (just-inj (snd (snd hr)))) = v₁ , f₁ , getRef-update-false-≡ {w1} v₁ f₁ i , λ x → x₁
... | no p = v , false , getRef-update-¬≡ {w1} n v₁ f₁ p i , λ x → x
⊑-pres-getRef {w1} {.(cell n r₁ (Res.def r₁) false ∷ w1)} {name} {r} {v} {f} (new .w1 n r₁ x) i with name ≟ n
... | yes p rewrite p | ¬∈wdom→getRef-nothing {n} {w1} x = ⊥-elim (¬just≡nothing (sym i))
... | no p = v , f , i , λ x → x



⊑-compatibleRef : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatibleRef c w1 r → compatibleRef c w2 r
⊑-compatibleRef {c} {w1} {w2} {r} e (v , f , comp , sat) =
  fst x , fst (snd x) , fst (snd (snd x)) , snd (snd (snd x)) sat
  where
    x : Σ Term (λ v' → Σ Bool (λ f' → getRef c w2 ≡ just (cell c r v' f') × pres-resSatRef v v' r))
    x = ⊑-pres-getRef e comp



startRefChoiceCompatible : (r : Res{0ℓ}) (w : 𝕎·) → compatibleRef (newRefChoice w) (startNewRefChoice r w) r
startRefChoiceCompatible r w =
  Res.def r , false , getRef-newCell w (newRefChoice w) r , Res.sat r



freezeRef : (n : Name) (w : 𝕎·) (v : Term) → world
freezeRef n w v = update n v true w


hasRes∷ : (name : Name) (r : Res) (v : Term) (f : Bool) (w : 𝕎·)
          → hasRes name (cell name r v f ∷ w) r
hasRes∷ name r v f w with name ≟ name
... | yes p = v , f , refl
... | no p = ⊥-elim (p refl)


freezableRef : (c : Name) (w : 𝕎·) → Set
freezableRef c w with getRef c w
... | just (cell n r v false) = ⊤
... | _ = ⊥


⊑-freeze∷ : (name : Name) (r : Res) (v₁ v₂ : Term) (w : 𝕎·)
         → ⋆ᵣ r v₂
         → (cell name r v₁ false ∷ w) ⊑· (cell name r v₂ true ∷ w)
⊑-freeze∷ name r v₁ v₂ w sat =
  ⊑-trans· (upd (cell name r v₁ false ∷ w) name r v₂ true (hasRes∷ name r v₁ false w) sat) z
  where
    z : (update name v₂ true (cell name r v₁ false ∷ w)) ⊑· (cell name r v₂ true ∷ w)
    z with name ≟ name
    ... | yes p = ⊑-refl· _
    ... | no p = ⊥-elim (p refl)


wdom++ : (w1 w2 : 𝕎·) → wdom (w1 ++ w2) ≡ wdom w1 ++ wdom w2
wdom++ [] w2 = refl
wdom++ (x ∷ w1) w2 rewrite wdom++ w1 w2 = refl


getRef++-¬∈ : {name : Name} (w1 w2 : 𝕎·)
              → ¬ name ∈ wdom w1
              → getRef name (w1 ++ w2) ≡ getRef name w2
getRef++-¬∈ {name} [] w2 ni = refl
getRef++-¬∈ {name} (cell name₁ r v f ∷ w1) w2 ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = getRef++-¬∈ w1 w2 (λ x → ni (there x))


hasRes++-¬∈ : {name : Name} (w1 w2 : 𝕎·) (r : Res)
              → ¬ name ∈ wdom w1
              → hasRes name w2 r
              → hasRes name (w1 ++ w2) r
hasRes++-¬∈ {name} w1 w2 r ni hr rewrite getRef++-¬∈ w1 w2 ni = hr


update++-¬∈ : {name : Name} {w1 : 𝕎·} (w2 : 𝕎·) (t : Term) (f : Bool)
              → ¬ name ∈ wdom w1
              → update name t f (w1 ++ w2) ≡ w1 ++ update name t f w2
update++-¬∈ {name} {[]} w2 t f ni = refl
update++-¬∈ {name} {cell name₁ r v f₁ ∷ w1} w2 t f ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p rewrite update++-¬∈ {name} {w1} w2 t f (λ x → ni (there x)) = refl


preFreezeRef⊑ : (c : Name) (w w' : 𝕎·) (t : Term) {r : Res}
                → compatibleRef c w r
                → ⋆ᵣ r t
                → ¬ (c ∈ wdom w')
                → (w' ++ w) ⊑· (w' ++ freezeRef c w t)
preFreezeRef⊑ c (cell name r₁ v₁ f₁ ∷ w) w' t {r} (v , f , comp , sat) rt ni with c ≟ name
preFreezeRef⊑ c (cell name r₁ v₁ true ∷ w) w' t {r} (v , f , comp , sat) rt ni | yes p rewrite p = ≼-refl _
preFreezeRef⊑ c (cell name r₁ v₁ false ∷ w) w' t {r} (v , f , comp , sat) rt ni | yes p
  rewrite p | sym (cell-inj2 (just-inj comp)) =
  ⊑-trans·
    (upd (w' ++ cell name r₁ v₁ false ∷ w) name r₁ t true hr' rt)
    e' --⊑-freeze∷ name r₁ v₁ t w rt
  where
    hr' : hasRes name (w' ++ cell name r₁ v₁ false ∷ w) r₁
    hr' = hasRes++-¬∈ w' (cell name r₁ v₁ false ∷ w) r₁ ni (hasRes∷ _ _ _ _ _)

    e' : update name t true (w' ++ cell name r₁ v₁ false ∷ w) ⊑· (w' ++ cell name r₁ t true ∷ w)
    e' rewrite update++-¬∈ {name} {w'} (cell name r₁ v₁ false ∷ w) t true ni with name ≟ name
    ... | yes q = ⊑-refl· _
    ... | no q = ⊥-elim (q refl)
preFreezeRef⊑ c (cell name r₁ v₁ f₁ ∷ w) w' t {r} (v , f , comp , sat) rt ni | no p
  rewrite sym (++-assoc w' [ cell name r₁ v₁ f₁ ] w)
        | sym (++-assoc w' [ cell name r₁ v₁ f₁ ] (freezeRef c w t)) =
  preFreezeRef⊑ c w (w' ++ [ cell name r₁ v₁ f₁ ]) t (v , f , comp , sat) rt ni'
  where
    ni' : ¬ c ∈ wdom (w' ++ [ cell name r₁ v₁ f₁ ])
    ni' i rewrite wdom++ w' [ cell name r₁ v₁ f₁ ] with ∈-++⁻ (wdom w') i
    ... | inj₁ q = ⊥-elim (ni q)
    ... | inj₂ (here q) = ⊥-elim (p q)


freezeRef⊑ : (c : Name) (w : 𝕎·) (t : Term) {r : Res} → compatibleRef c w r → ⋆ᵣ r t → w ⊑· freezeRef c w t
freezeRef⊑ c w t {r} comp sat = preFreezeRef⊑ c w [] t comp sat λ ()


getFreezeRef : (c : Name) (w : 𝕎·) (t : Term) {r : Res{0ℓ}}
               → compatibleRef c w r
               → freezableRef c w
               → Σ ℕ (λ n → ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (getRefChoice n c w' ≡ just t)))
getFreezeRef c w t {r} (v , f , comp , sat) fb = 0 , aw
  where
    aw : ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (getRefChoice 0 c w' ≡ just t))
    aw w1 e1 = lift {!!}
 {--
  length l , aw
  where
    aw : ∀𝕎 (freezeCs c w t) (λ w' _ → Lift 2ℓ (getCsChoice (length l) c w' ≡ just t))
    aw w1 e1 = lift (≽-pres-getChoice e1 g)
      where
        g : getCsChoice (length l) c (freezeCs c w t) ≡ just t
        g rewrite getCs++-same-choice c w l r t comp | select-last l t = refl
--}


getRef⊎ : (name : Name) (w : world)
           → Σ Cell (λ c → getRef name w ≡ just c)
              ⊎ getRef name w ≡ nothing
getRef⊎ name w with getRef name w
... | just c = inj₁ (c , refl)
... | nothing = inj₂ refl


freezableStartRef : (r : Res{0ℓ}) (w : 𝕎·) → freezableRef (newRefChoice w) (startNewRefChoice r w)
freezableStartRef r w with newRefChoice w ≟ newRefChoice w
... | yes p = tt
... | no p = ⊥-elim (p refl)


progressRef : (c : Name) (w1 w2 : 𝕎·) → Set₁
progressRef c w1 w2 =
  (r : Res) (v : Term) (f : Bool)
  → ∈world c r v f w1
  → Σ Term (λ v' → Σ Bool (λ f' → ∈world c r v' f' w2 × satFrozen v v' f f'))


freezeRefProgress : (c : Name) {w1 w2 : 𝕎·} (t : Term) → w1 ⊑· w2 → progressRef c w1 (freezeRef c w2 t)
freezeRefProgress c {w1} {w2} t e r v f i = {!!}


refChoice : Choice
refChoice =
  mkChoice
    getRefChoice
    newRefChoice
    startRefChoice
    getRefChoice-startNewRefChoice
    startNewRefChoice⊏
    compatibleRef
    ⊑-compatibleRef
    startRefChoiceCompatible
    freezeRef
    freezableRef
    freezeRef⊑
    getFreezeRef
    freezableStartRef
    progressRef
    freezeRefProgress
    {!!}
    {!!}


\end{code}
