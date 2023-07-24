\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Bool using (Bool ; _∧_ ; _∨_ ; true ; false ; if_then_else_)
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
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import terms


module worldInstanceRef (E : Extensionality 0ℓ 0ℓ) where
\end{code}



This provides an instance of world and choice for choice sequences


\begin{code}
B→C : Bool → CTerm
B→C true = #NUM 0
B→C false = #NUM 1


B→C-inj : {a b : Bool} → B→C a ≡ B→C b → a ≡ b
B→C-inj {false} {false} x = refl
B→C-inj {true} {true} x = refl


ℕ→C : ℕ → CTerm
ℕ→C n = #NUM n


ℕ→C-inj : {a b : ℕ} → ℕ→C a ≡ ℕ→C b → a ≡ b
ℕ→C-inj {a} {b} h = NUMinj (≡CTerm h)



-- We could use Bools instead but then in choiceBarInstance.lagda, we have to pick a better type that contains only choices.
-- Could instead ∈Typeℂ₀₁→ in choiceBar have an assumption about a and b being choices?
open import choice

choiceRef : Choice
--choiceRef = mkChoice Bool B→C B→C-inj
choiceRef = mkChoice ℕ ℕ→C (λ c → refl) (λ c → refl) --ℕ→C-inj

open import choiceDef{1ℓ}(choiceRef)



-- The Bool says whether the cell is "frozen"
record Cell : Set₁ where
  constructor cell
  field
    name : Name
    r : Res{0ℓ}
    v : ℂ·
    f : Bool


-- Worlds - entries are added at the end of the list
world : Set₁
world = List Cell


wdom : world → List Name
wdom [] = []
wdom (cell name _ _ _ ∷ w) = name ∷ wdom w


wnames : world → List Name
wnames w = []


update : (n : Name) (v : ℂ·) (f : Bool) (w : world) → world
update _ _ _ [] = []
update n v f (cell name r x b ∷ w) with n ≟ name
... | yes p = (if b ∧ Res.frz r then cell name r x b else cell name r v f) ∷ w
... | no p = cell name r x b ∷ update n v f w


newCell : (n : Name) (r : Res{0ℓ}) (w : world) → world
newCell n r w = cell n r (Res.def r) false ∷ w


getRef : Name → world → Maybe Cell
getRef name [] = nothing
getRef name (cell n r v f ∷ w) with name ≟ n
... | yes p = just (cell n r v f)
... | no p = getRef name w


∈world : (n : Name) (r : Res{0ℓ}) (v : ℂ·) (f : Bool) (w : world) → Set₁
∈world n r v f w = getRef n w ≡ just (cell n r v f)


hasRes : (c : Name) (w : world) (r : Res{0ℓ}) → Set₁
hasRes c w r = Σ ℂ· (λ v → Σ Bool (λ f → ∈world c r v f w))


data _≼_ : (w2 : world) (w1 : world) → Set₁ where
  ≼-refl : (w : world) → w ≼ w
  ≼-trans : {w1 w2 w3 : world} → w1 ≼ w2 → w2 ≼ w3 → w1 ≼ w3
  upd :
    (w : world) (n : Name) (r : Res{0ℓ}) (v : ℂ·) (f : Bool)
    → hasRes n w r
    → ⋆ᵣ r v
--    → ·ᵣ r 0 v
    → w ≼ update n v f w
  new :
    (w : world) (n : Name) (r : Res{0ℓ})
    → ¬ (n ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → w ≼ newCell n r w



open import world

PossibleWorldsRef : PossibleWorlds
PossibleWorldsRef = mkPossibleWorlds world _≼_ ≼-refl ≼-trans

open import worldDef(PossibleWorldsRef)



resSatRef : (v : ℂ·) (r : Res{0ℓ}) → Set
resSatRef v r = ⋆ᵣ r v -- ·ᵣ r 0 v


-- This is the same as 'hasRef' & enforces satisfiability too
compatibleRef : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set₁
compatibleRef c w r = Σ ℂ· (λ v → Σ Bool (λ f → ∈world c r v f w × resSatRef v r))



pres-resSatRef : (v v' : ℂ·) (r : Res{0ℓ}) → Set
pres-resSatRef v v' r = resSatRef v r → resSatRef v' r


pres-resSatRef-refl : (v : ℂ·) (r : Res{0ℓ}) → pres-resSatRef v v r
pres-resSatRef-refl v r d = d


pres-resSatRef-trans : {v1 v2 v3 : ℂ·} {r : Res{0ℓ}}
                       → pres-resSatRef v1 v2 r
                       → pres-resSatRef v2 v3 r
                       → pres-resSatRef v1 v3 r
pres-resSatRef-trans {v1} {v2} {v3} {r} p1 p2 s = p2 (p1 s)



satFrozen : (r : Res{0ℓ}) (v v' : ℂ·) (f f' : Bool) → Set
satFrozen r v v' true f' = (Res.frz r ≡ true → f' ≡ true × v ≡ v')
satFrozen r v v' false f' = ⊤


satFrozen-refl : (r : Res{0ℓ}) (v : ℂ·) (f : Bool) → satFrozen r v v f f
satFrozen-refl r v true = λ _ → refl , refl
satFrozen-refl r v false = tt


satFrozen-trans : {r : Res{0ℓ}} {v1 v2 v3 : ℂ·} {f1 f2 f3 : Bool}
                  → satFrozen r v1 v2 f1 f2
                  → satFrozen r v2 v3 f2 f3
                  → satFrozen r v1 v3 f1 f3
satFrozen-trans {r} {v1} {v2} {v3} {false} {f2} {f3} s1 s2 = tt
satFrozen-trans {r} {v1} {v2} {v3} {true} {f2} {f3} s1 s2 z rewrite z | fst (s1 refl) | snd (s1 refl) = s2 z


cell-inj1 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : ℂ·} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → n1 ≡ n2
cell-inj1 refl =  refl


cell-inj2 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : ℂ·} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → r1 ≡ r2
cell-inj2 refl =  refl


cell-inj3 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : ℂ·} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → v1 ≡ v2
cell-inj3 refl =  refl


cell-inj4 : {n1 n2 : Name} {r1 r2 : Res} {v1 v2 : ℂ·} {f1 f2 : Bool} → cell n1 r1 v1 f1 ≡ cell n2 r2 v2 f2 → f1 ≡ f2
cell-inj4 refl =  refl


getRef-update-true-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·) (f : Bool)
                       → Rfrz? r
                       → getRef name w ≡ just (cell name r v true)
                       → getRef name (update name v' f w) ≡ just (cell name r v true)
getRef-update-true-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name₁ ≟ name₁
...     | yes q with Res.frz r
...        | true rewrite q with name₁ ≟ name₁
...           | yes s = refl
...           | no s = ⊥-elim (s q)
getRef-update-true-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | yes p | yes q | false rewrite q = ⊥-elim frz
getRef-update-true-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | yes p | no q = ⊥-elim (q refl)
getRef-update-true-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | no p with name ≟ name₁
...     | yes q = ⊥-elim (p q)
...     | no q = getRef-update-true-≡ {w} v' f frz e



getRef-update-true-¬frz-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·) (f : Bool)
                       → ¬ (Rfrz? r)
                       → getRef name w ≡ just (cell name r v true)
                       → getRef name (update name v' f w) ≡ just (cell name r v' f)
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with Res.frz r
... |    true = ⊥-elim (frz tt)
... |    false with name₁ ≟ name₁
... |       yes q rewrite q = refl
... |       no q = ⊥-elim (q refl)
getRef-update-true-¬frz-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f frz e | no p with name ≟ name₁
... |    yes q = ⊥-elim (p q)
... |    no q = getRef-update-true-¬frz-≡ {w} v' f frz e



getRef-update-false-≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} (v' : ℂ·) (f : Bool)
                     → getRef name w ≡ just (cell name r v false)
                     → getRef name (update name v' f w) ≡ just (cell name r v' f)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f e with name ≟ name₁
... | yes p rewrite p | cell-inj2 (just-inj e) | cell-inj3 (just-inj e) | cell-inj4 (just-inj e) with name₁ ≟ name₁
...     | yes q = refl --refl
...     | no q = ⊥-elim (q refl)
getRef-update-false-≡ {cell name₁ r₁ v₁ f₁ ∷ w} {name} {r} {v} v' f e | no p with name ≟ name₁
...     | yes q = ⊥-elim (p q)
...     | no q = getRef-update-false-≡ {w} v' f e



getRef-update-¬≡ : {w : 𝕎·} {name : Name} {r : Res{0ℓ}} {v : ℂ·} {f : Bool} (name' : Name) (v' : ℂ·) (f' : Bool)
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
... |       no z with Res.frz r₁
... |          true with name ≟ name₁
... |             yes s = ⊥-elim (z s)
... |             no s = e
getRef-update-¬≡ {cell name₁ r₁ v₁ true ∷ w} {name} {r} {v} {f} name' v' f' d e | no p | yes q | no z | false with name ≟ name₁
... |             yes s = ⊥-elim (p s)
... |             no s = e
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


bool⊎ : (b : Bool) → b ≡ true ⊎ b ≡ false
bool⊎ true = inj₁ refl
bool⊎ false = inj₂ refl


→Rfrz? : {r : Res{0ℓ}} → Res.frz r ≡ true → Rfrz? r
→Rfrz? {r} e rewrite e = tt


Rfrz?→ : {r : Res{0ℓ}} → Rfrz? r → Res.frz r ≡ true
Rfrz?→ {r} e with Res.frz r
... | true = refl
... | false = ⊥-elim e


→¬Rfrz? : {r : Res{0ℓ}} → Res.frz r ≡ false → ¬ Rfrz? r
→¬Rfrz? {r} e rewrite e = λ z → z


⊑-pres-getRef : {w1 w2 : world} {name : Name} {r : Res} {v : ℂ·} {f : Bool}
                 → w1 ⊑· w2
                 → getRef name w1 ≡ just (cell name r v f)
                 → Σ ℂ· (λ v' → Σ Bool (λ f' → getRef name w2 ≡ just (cell name r v' f') × pres-resSatRef v v' r × satFrozen r v v' f f'))
⊑-pres-getRef {w1} {.w1} {name} {r} {v} {f} (≼-refl .w1) i = v , f , i , pres-resSatRef-refl v r , satFrozen-refl r v f
⊑-pres-getRef {w1} {w3} {name} {r} {v} {f} (≼-trans {.w1} {w2} {.w3} e₁ e₂) i =
  fst ind2 , fst (snd ind2) , fst (snd (snd ind2)) ,
  pres-resSatRef-trans {v} {fst ind1} {fst ind2} {r} (fst (snd (snd (snd ind1)))) (fst (snd (snd (snd ind2)))) ,
  satFrozen-trans (snd (snd (snd (snd ind1)))) (snd (snd (snd (snd ind2))))
  where
    ind1 : Σ ℂ· (λ v' → Σ Bool (λ f' → getRef name w2 ≡ just (cell name r v' f') × pres-resSatRef v v' r × satFrozen r v v' f f'))
    ind1 = ⊑-pres-getRef e₁ i

    ind2 : Σ ℂ· (λ v' → Σ Bool (λ f' → getRef name w3 ≡ just (cell name r v' f') × pres-resSatRef (fst ind1) v' r × satFrozen r (fst ind1) v' (fst (snd ind1)) f'))
    ind2 = ⊑-pres-getRef e₂ (fst (snd (snd ind1)))
⊑-pres-getRef {w1} {.(update n v₁ f₁ w1)} {name} {r} {v} {true} (upd .w1 n r₁ v₁ f₁ hr x) i with n ≟ name
... | yes p rewrite p with bool⊎ (Res.frz r)
... |    inj₁ s rewrite s =
  v , true , (getRef-update-true-≡ {w1} v₁ f₁ (→Rfrz? {r} s) i) , (λ x → x) , (λ _ → refl , refl)
... |    inj₂ s rewrite s | i | sym (cell-inj2 (just-inj (snd (snd hr)))) =
  v₁ , f₁ , (getRef-update-true-¬frz-≡ {w1} v₁ f₁ (→¬Rfrz? {r} s) i) , (λ z → x) , (λ ())
⊑-pres-getRef {w1} {.(update n v₁ f₁ w1)} {name} {r} {v} {true} (upd .w1 n r₁ v₁ f₁ hr x) i | no p =
  v , true , getRef-update-¬≡ {w1} n v₁ f₁ p i , (λ x → x) , λ z → refl , refl
⊑-pres-getRef {w1} {.(update n v₁ f₁ w1)} {name} {r} {v} {false} (upd .w1 n r₁ v₁ f₁ hr x₁) i with n ≟ name
... | yes p rewrite p | i | sym (cell-inj2 (just-inj (snd (snd hr)))) = v₁ , f₁ , getRef-update-false-≡ {w1} v₁ f₁ i , (λ x → x₁) , tt
... | no p = v , false , getRef-update-¬≡ {w1} n v₁ f₁ p i , (λ x → x) , tt
⊑-pres-getRef {w1} {.(cell n r₁ (Res.def r₁) false ∷ w1)} {name} {r} {v} {f} (new .w1 n r₁ x) i with name ≟ n
... | yes p rewrite p | ¬∈wdom→getRef-nothing {n} {w1} x = ⊥-elim (¬just≡nothing (sym i))
... | no p = v , f , i , (λ x → x) , satFrozen-refl r v f



⊑-compatibleRef : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatibleRef c w1 r → compatibleRef c w2 r
⊑-compatibleRef {c} {w1} {w2} {r} e (v , f , comp , sat) =
  fst x , fst (snd x) , fst (snd (snd x)) , fst (snd (snd (snd x))) sat
  where
    x : Σ ℂ· (λ v' → Σ Bool (λ f' → getRef c w2 ≡ just (cell c r v' f') × pres-resSatRef v v' r × satFrozen r v v' f f'))
    x = ⊑-pres-getRef e comp



open import compatible(PossibleWorldsRef)(choiceRef)

compatibleREF : Compatible
compatibleREF = mkCompatible compatibleRef ⊑-compatibleRef

open import compatibleDef(PossibleWorldsRef)(choiceRef)(compatibleREF)



getRefChoice : (n : ℕ) (name : Name) (w : world) → Maybe ℂ·
getRefChoice _ name w with getRef name w
... | just (cell _ _ v _) = just v
... | nothing = nothing



getRefChoiceCompatible : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) (n : ℕ) (t : ℂ·)
                        → compatibleRef c w r → getRefChoice n c w ≡ just t → ·ᵣ r n t
getRefChoiceCompatible c r w n t (k , b , i , sat) g rewrite i | just-inj g = sat n



-- We're really only generating numbers as choices here
T→ℂref : Term → ℂ·
T→ℂref (NUM n) = n
T→ℂref _ = 0


getRef⊎ : (name : Name) (w : world)
           → Σ Cell (λ c → getRef name w ≡ just c)
              ⊎ getRef name w ≡ nothing
getRef⊎ name w with getRef name w
... | just c = inj₁ (c , refl)
... | nothing = inj₂ refl


chooseREF : (cs : Name) (w : 𝕎·) (c : ℂ·) → 𝕎·
chooseREF n w c with getRef n w
... | just (cell name r v f) with Res.dec r
... |    (true , D) with Res.inv r
... |       (true , I) with D 0 c
... |          inj₁ y = update n c f w
... |          inj₂ y = w
chooseREF n w c | just (cell name r v f) | (true , _) | (false , _) = w
chooseREF n w c | just (cell name r v f) | (false , _) = w
chooseREF n w c | nothing = w


getRef→∈world : {n name : Name} {w : 𝕎·} {r : Res} {v : ℂ·} {f : Bool}
                 → getRef n w ≡ just (cell name r v f)
                 → ∈world n r v f w
getRef→∈world {n} {name} {cell name₁ r₁ v₁ f₁ ∷ w} {r} {v} {f} h with n ≟ name₁
... | yes p rewrite p | h | cell-inj1 (just-inj h) = refl
... | no p = getRef→∈world {n} {name} {w} h



chooseREF⊑ : (cs : Name) (w : 𝕎·) (c : ℂ·) → w ⊑· chooseREF cs w c
chooseREF⊑ n w c with getRef⊎ n w
... | inj₁ (cell name r v f , e) rewrite e with Res.dec r
... |    (true , D) with Res.inv r
... |       (true , I) with D 0 c
... |          inj₁ y = upd w n r c f (v , f , getRef→∈world {n} {name} {w} e) (inv→·ᵣ→⋆ᵣ {r} {c} I y)
... |          inj₂ y = ⊑-refl· _
chooseREF⊑ n w c | inj₁ (cell name r v f , e) | (true , _) | (false , _ ) rewrite e = ⊑-refl· _
chooseREF⊑ n w c | inj₁ (cell name r v f , e) | (false , _) rewrite e = ⊑-refl· _
chooseREF⊑ n w c | inj₂ e rewrite e = ⊑-refl· _


isℂ₀ref : ℂ· → Bool
isℂ₀ref 0 = true
isℂ₀ref (suc _) = false


open import getChoice(PossibleWorldsRef)(choiceRef)(compatibleREF)

getChoiceRef : GetChoice
getChoiceRef = mkGetChoice getRefChoice T→ℂref chooseREF chooseREF⊑
-- wdom
-- isℂ₀ref
-- getRefChoiceCompatible

open import getChoiceDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(getChoiceRef)




progressRef : (c : Name) (w1 w2 : 𝕎·) → Set₁
progressRef c w1 w2 =
  (r : Res) (v : ℂ·) (f : Bool)
  → ∈world c r v f w1
  → Σ ℂ· (λ v' → Σ Bool (λ f' → ∈world c r v' f' w2 × satFrozen r v v' f f'))


progressRef-refl : (c : Name) (w : 𝕎·) → progressRef c w w
progressRef-refl c w r v f i = v , f , i , satFrozen-refl r v f


progressRef-trans : {c : Name} {w1 w2 w3 : 𝕎·}
                    → progressRef c w1 w2
                    → progressRef c w2 w3
                    → progressRef c w1 w3
progressRef-trans {c} {w1} {w2} {w3} p1 p2 r v f i =
  fst z2 , fst (snd z2) , fst (snd (snd z2)) , satFrozen-trans (snd (snd (snd z1))) (snd (snd (snd z2)))
  where
    z1 : Σ ℂ· (λ v' → Σ Bool (λ f' → ∈world c r v' f' w2 × satFrozen r v v' f f'))
    z1 = p1 r v f i

    z2 : Σ ℂ· (λ v' → Σ Bool (λ f' → ∈world c r v' f' w3 × satFrozen r (fst z1) v' (fst (snd (z1))) f'))
    z2 = p2 r (fst z1) (fst (snd z1)) (fst (snd (snd z1)))


𝕎→refChain : (w : 𝕎·) → chain w
𝕎→refChain w = mkChain (λ _ → w) (⊑-refl· _) λ _ → ⊑-refl· _


refChainProgress : (w : 𝕎·) (x : Name) (n : ℕ) {r : Res{0ℓ}}
                   → compatibleRef x (chain.seq (𝕎→refChain w) n) r
                   → Σ ℕ (λ m → n < m × progressRef x (chain.seq (𝕎→refChain w) n) (chain.seq (𝕎→refChain w) m))
refChainProgress w x n {r} (v , f , i , sat) = suc n , ≤-refl , progressRef-refl x w




open import progress(PossibleWorldsRef)(choiceRef)(compatibleREF)

progressREF : Progress
progressREF =
  mkProgress
    progressRef
    𝕎→refChain
    refChainProgress

open import progressDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)



C0 : ℂ·
C0 = 0 --true


C1 : ℂ·
C1 = 1 --false

decℂ₀ref : (c : ℂ·) → c ≡ C0 ⊎ ¬ c ≡ C0
decℂ₀ref c with c ≟ 0
... | yes x rewrite x = inj₁ refl
... | no x = inj₂ λ y → x y


decℂ₁ref : (c : ℂ·) → c ≡ C1 ⊎ ¬ c ≡ C1
decℂ₁ref c with c ≟ 1
... | yes x rewrite x = inj₁ refl
... | no x = inj₂ λ y → x y



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
                 → getRef name (newCell name r w) ≡ just (cell name r (Res.def r) false)
getRef-newCell w name r with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)


getRefChoice-startRefChoice : (n : ℕ) (r : Res) (w : 𝕎·) (t : ℂ·) (name : Name)
                              → ¬ name ∈ wdom w
                              → getRefChoice n name (startRefChoice name r w) ≡ just t → t ≡ Res.def r
--                            → getRefChoice n (newRefChoice w) (startNewRefChoice r w) ≡ nothing
getRefChoice-startRefChoice n r w t name ni e
  rewrite getRef-newCell w name r
        | just-inj e = refl


startRefChoice⊏ : (r : Res) (w : 𝕎·) (name : Name) → ¬ name ∈ wdom w → w ⊑· startRefChoice name r w
startRefChoice⊏ r w name ni = new w name r ni



startRefChoiceCompatible : (r : Res{0ℓ}) (w : 𝕎·) (name : Name) → ¬ name ∈ wdom w → compatibleRef name (startRefChoice name r w) r
startRefChoiceCompatible r w name ni =
  Res.def r , false , getRef-newCell w name r , Res.sat r



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
freezeRef n w v = update n v true w


hasRes∷ : (name : Name) (r : Res) (v : ℂ·) (f : Bool) (w : 𝕎·)
          → hasRes name (cell name r v f ∷ w) r
hasRes∷ name r v f w with name ≟ name
... | yes p = v , f , refl
... | no p = ⊥-elim (p refl)


freezableRef : (c : Name) (w : 𝕎·) → Set
freezableRef c w with getRef c w
... | just (cell n r v false) = ⊤
... | _ = ⊥


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


update++-¬∈ : {name : Name} {w1 : 𝕎·} (w2 : 𝕎·) (t : ℂ·) (f : Bool)
              → ¬ name ∈ wdom w1
              → update name t f (w1 ++ w2) ≡ w1 ++ update name t f w2
update++-¬∈ {name} {[]} w2 t f ni = refl
update++-¬∈ {name} {cell name₁ r v f₁ ∷ w1} w2 t f ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p rewrite update++-¬∈ {name} {w1} w2 t f (λ x → ni (there x)) = refl


preFreezeRef⊑ : (c : Name) (w w' : 𝕎·) (t : ℂ·) {r : Res}
                → compatibleRef c w r
                → ⋆ᵣ r t
                → ¬ (c ∈ wdom w')
                → (w' ++ w) ⊑· (w' ++ freezeRef c w t)
preFreezeRef⊑ c (cell name r₁ v₁ f₁ ∷ w) w' t {r} (v , f , comp , sat) rt ni with c ≟ name
preFreezeRef⊑ c (cell name r₁ v₁ true ∷ w) w' t {r} (v , f , comp , sat) rt ni | yes p
  rewrite p with bool⊎ (Res.frz r₁)
... | inj₁ s rewrite s = ≼-refl _
... | inj₂ s rewrite s | sym (cell-inj2 (just-inj comp)) =
  ⊑-trans· (upd (w' ++ cell name r₁ v₁ true ∷ w) name r₁ t true hr' rt) e'
  where
    hr' : hasRes name (w' ++ cell name r₁ v₁ true ∷ w) r₁
    hr' = hasRes++-¬∈ w' (cell name r₁ v₁ true ∷ w) r₁ ni (hasRes∷ _ _ _ _ _)

    e' : update name t true (w' ++ cell name r₁ v₁ true ∷ w) ⊑· (w' ++ cell name r₁ t true ∷ w)
    e' rewrite update++-¬∈ {name} {w'} (cell name r₁ v₁ true ∷ w) t true ni with name ≟ name
    ... | yes q rewrite s = ⊑-refl· _
    ... | no q = ⊥-elim (q refl)
preFreezeRef⊑ c (cell name r₁ v₁ false ∷ w) w' t {r} (v , f , comp , sat) rt ni | yes p
  rewrite p | sym (cell-inj2 (just-inj comp)) =
  ⊑-trans· (upd (w' ++ cell name r₁ v₁ false ∷ w) name r₁ t true hr' rt) e'
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


freezeRef⊑ : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res} → compatibleRef c w r → ⋆ᵣ r t → w ⊑· freezeRef c w t
freezeRef⊑ c w t {r} comp sat = preFreezeRef⊑ c w [] t comp sat λ ()


freezableStartRef : (r : Res{0ℓ}) (w : 𝕎·) → freezableRef (newRefChoice w) (startNewRefChoice r w)
freezableStartRef r w with newRefChoice w ≟ newRefChoice w
... | yes p = tt
... | no p = ⊥-elim (p refl)



progressFreeze : (c : Name) (w1 w2 : 𝕎·) → Set₁
progressFreeze c w1 w2 =
  (r : Res) (v : ℂ·) (f : Bool)
  → ∈world c r v f w1
  → Σ ℂ· (λ v' → ∈world c r v' true w2 × satFrozen r v v' f true)



progressRef-freeze : (c : Name) (w : 𝕎·) (t : ℂ·) → progressFreeze c w (freezeRef c w t)
progressRef-freeze c (cell name r₁ v₁ f₁ ∷ w) t r v f i with c ≟ name
progressRef-freeze c (cell name r₁ v₁ true ∷ w) t r v f i | yes p
  rewrite p | sym (cell-inj2 (just-inj i)) | sym (cell-inj3 (just-inj i)) | sym (cell-inj4 (just-inj i)) with Res.frz r₁
... |    true with name ≟ name
... |       yes q = v₁ , refl , λ z → refl , refl
... |       no q = ⊥-elim (q refl)
progressRef-freeze c (cell name r₁ v₁ true ∷ w) t r v f i | yes p | false with name ≟ name
... |       yes q = t , refl , λ ()
... |       no q = ⊥-elim (q refl)
progressRef-freeze c (cell name r₁ v₁ false ∷ w) t r v f i | yes p rewrite p with name ≟ name
... |   yes q rewrite q | sym (cell-inj2 (just-inj i)) | sym (cell-inj3 (just-inj i)) | sym (cell-inj4 (just-inj i)) =
  t , refl , tt
... |   no q = ⊥-elim (q refl)
progressRef-freeze c (cell name r₁ v₁ f₁ ∷ w) t r v f i | no p with c ≟ name
... |   yes q rewrite q = ⊥-elim (p refl)
... |   no q = progressRef-freeze c w t r v f i





⊑→progressRef : (c : Name) {w1 w2 : 𝕎·} → w1 ⊑· w2 → progressRef c w1 w2
⊑→progressRef c {w1} {w2} e r v f i =
  fst (⊑-pres-getRef e i) ,
  fst (snd (⊑-pres-getRef e i)) ,
  fst (snd (snd (⊑-pres-getRef e i))) ,
  snd (snd (snd (snd (⊑-pres-getRef e i))))



∈world-false-freezeRef-true : (c : Name) (r : Res) (v : ℂ·) (w : 𝕎·) (t : ℂ·)
                              → ∈world c r v false w
                              → ∈world c r t true (freezeRef c w t)
∈world-false-freezeRef-true c r v (cell name r₁ v₁ f ∷ w) t i with c ≟ name
∈world-false-freezeRef-true c r v (cell name r₁ v₁ true ∷ w) t i | yes p rewrite p with name ≟ name
... |   yes q rewrite q = ⊥-elim (z2 z1)
  where
    z1 : true ≡ false
    z1 = cell-inj4 (just-inj i)

    z2 : true ≡ false → ⊥
    z2 ()
... |   no q = ⊥-elim (q refl)
∈world-false-freezeRef-true c r v (cell name r₁ v₁ false ∷ w) t i | yes p rewrite p with name ≟ name
... |   yes q rewrite q | cell-inj2 (just-inj i) = refl
... |   no q = ⊥-elim (q refl)
∈world-false-freezeRef-true c r v (cell name r₁ v₁ f ∷ w) t i | no p with c ≟ name
... |   yes q rewrite q = ⊥-elim (p refl)
... |   no q = ∈world-false-freezeRef-true c r v w t i



freeze→¬freezable : {c : Name} {w : 𝕎·} {r : Res{0ℓ}} (t : ℂ·)
                    → compatibleRef c w r
                    → Rfrz? r
                    → ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (¬ freezableRef c w'))
freeze→¬freezable {c} {w} {r} t (v , f , comp , sat) frz w1 e1 = lift z4
  where
    z1 : Σ ℂ· (λ v' → ∈world c r v' true (freezeRef c w t) × satFrozen r v v' f true)
    z1 = progressRef-freeze c w t r v f comp

    z2 : Σ ℂ· (λ v' → Σ Bool (λ f' → ∈world c r v' f' w1 × satFrozen r (fst z1) v' true f'))
    z2 = ⊑→progressRef c e1 r (fst z1) true (fst (snd z1))

    z3 : ∈world c r (fst z1) true w1
    z3 rewrite fst (snd (snd z2))
             | fst (snd (snd (snd z2)) (Rfrz?→ {r} frz))
             | sym (snd (snd (snd (snd z2)) (Rfrz?→ {r} frz))) = refl

    z4 : ¬ freezableRef c w1
    z4 h rewrite z3 = h


--freeze→¬freezable c w t {r} (v , false , comp , sat) rewrite comp = {!!}



getFreezeRef-aux : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}}
                   → compatibleRef c w r
                   → Rfrz? r
                   → freezableRef c w
                   → Σ ℕ (λ n → ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (getRefChoice n c w' ≡ just t × ¬ freezableRef c w')))
getFreezeRef-aux c w t {r} (v , true , comp , sat) frz fb rewrite comp = ⊥-elim fb
getFreezeRef-aux c w t {r} (v , false , comp , sat) frz fb rewrite comp = 0 , aw
  where
    aw : ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (getRefChoice 0 c w' ≡ just t × ¬ freezableRef c w'))
    aw w1 e1 = lift (z4 , z5)
      where
        z1 : Σ ℂ· (λ v' → ∈world c r v' true (freezeRef c w t) × satFrozen r v v' false true)
        z1 = progressRef-freeze c w t r v false comp

        z2 : Σ ℂ· (λ v' → Σ Bool (λ f' → ∈world c r v' f' w1 × satFrozen r (fst z1) v' true f'))
        z2 = ⊑→progressRef c e1 r (fst z1) true (fst (snd z1))

        z3 : ∈world c r (fst z1) true w1
        z3 rewrite fst (snd (snd z2))
             | fst (snd (snd (snd z2)) (Rfrz?→ {r} frz))
             | sym (snd (snd (snd (snd z2)) (Rfrz?→ {r} frz))) = refl

        x : ∈world c r (fst z1) true (freezeRef c w t) → fst z1 ≡ t
        x i rewrite ∈world-false-freezeRef-true c r v w t comp = sym (cell-inj3 (just-inj i))

        z4 : getRefChoice 0 c w1 ≡ just t
        z4 rewrite z3 | x (fst (snd z1)) = refl

        z5 : ¬ freezableRef c w1
        z5 h rewrite z3 = h



getFreezeRef : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}}
               → compatibleRef c w r
               → Rfrz? r
               → freezableRef c w
               → Σ ℕ (λ n → ∀𝕎 (freezeRef c w t) (λ w' _ → Lift 2ℓ (getRefChoice n c w' ≡ just t)))
getFreezeRef c w t {r} comp frz fb =
  fst (getFreezeRef-aux c w t comp frz fb) ,
  λ w1 e1 → lift (fst (lower (snd (getFreezeRef-aux c w t comp frz fb) w1 e1)))



progressFreeze→progressRef : {c : Name} {w1 w2 : 𝕎·}
                              → progressFreeze c w1 w2
                              → progressRef c w1 w2
progressFreeze→progressRef {c} {w1} {w2} p r v f i =
  fst (p r v f i) , true , snd (p r v f i)



freezeRefProgress : (c : Name) {w1 w2 : 𝕎·} (t : ℂ·) → w1 ⊑· w2 → progressRef c w1 (freezeRef c w2 t)
freezeRefProgress c {w1} {w2} t e =
  progressRef-trans {c} {w1} {w2} {freezeRef c w2 t}
                    (⊑→progressRef c e)
                    (progressFreeze→progressRef {c} {w2} {freezeRef c w2 t} (progressRef-freeze c w2 t))



open import freeze(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(newChoiceRef)

freezeREF : Freeze
freezeREF =
  mkFreeze
    freezeRef
    freezableRef
    freezeRef⊑
    getFreezeRef
    freezableStartRef
    --freezeRefProgress

open import freezeDef(PossibleWorldsRef)(choiceRef)(compatibleREF)(progressREF)(getChoiceRef)(newChoiceRef)(freezeREF)

\end{code}
