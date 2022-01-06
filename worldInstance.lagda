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

open import util
open import calculus
open import world


module worldInstance where
\end{code}



This provides an instance of world and choice for choice sequences


\begin{code}
record cs : Set₁ where
  constructor mkcs
  field
    name    : Name
    choices : List Term
    res     : Res{0ℓ}


data entry : Set₁ where
  start  : (name : Name) (res : Res) → entry
  choice : (name : Name) (t : Term) → entry


-- Worlds - entries are added at the end of the list
world : Set₁
world = List entry


getChoices : Name → world → List Term
getChoices name [] = []
getChoices name (start _ _ ∷ w) = getChoices name w
getChoices name (choice n t ∷ w) with name ≟ n
... | yes p = t ∷ getChoices name w
... | no p = getChoices name w



-- ⟨_⟩_≽_ guarantees that there is only one 'start' for each choice sequence
getCs : Name → world → Maybe cs
getCs name [] = nothing
getCs name (start n r ∷ w) with name ≟ n
... | yes p = just (mkcs name (getChoices name w) r)
... | no p = getCs name w
getCs name (choice n t ∷ w) = getCs name w


wdom : world → List Name
wdom [] = []
wdom (start name _ ∷ w) = name ∷ wdom w
wdom (choice _ _ ∷ w) = wdom w


∈world : cs → world → Set₁
∈world e w = getCs (cs.name e) w ≡ just e


newcs : world → Name → Res → world
newcs w name r = w ∷ʳ start name r


extcs : world → Name → Term → world
extcs w name t = w ∷ʳ choice name t


-- w2 extends w1
data _≽_ : (w2 : world) (w1 : world) → Set₁ where
  extRefl : (w : world) → w ≽ w
  extTrans : {w1 w2 w3 : world} → w3 ≽ w2 → w2 ≽ w1 → w3 ≽ w1
  extChoice :
    (w : world) (name : Name) (l : List Term) (t : Term) (res : Res)
    → ∈world (mkcs name l res) w
    → res (length l) t
    → (extcs w name t) ≽ w
  extEntry :
    (w : world) (name : Name) (res : Res)
    → ¬ (name ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → (newcs w name res) ≽ w



-- An instance of PossibleWorlds
PossibleWorldsCS : PossibleWorlds
PossibleWorldsCS = mkPossibleWorlds world (λ w1 w2 → w2 ≽ w1) extRefl (λ {w1 w2 w3} e1 e2 → extTrans e2 e1)


open import worldDef(PossibleWorldsCS)



getChoices++ : (name : Name) (w w' : world)
               → getChoices name (w ++ w') ≡ getChoices name w ++ getChoices name w'
getChoices++ name [] w' = refl
getChoices++ name (start name₁ res ∷ w) w' = getChoices++ name w w'
getChoices++ name (choice name₁ t ∷ w) w' with name ≟ name₁
... | yes p rewrite getChoices++ name w w' = refl
... | no p = getChoices++ name w w'


getCs⊎ : (name : Name) (w : world) → (Σ cs (λ e → getCs name w ≡ just e)) ⊎ getCs name w ≡ nothing
getCs⊎ name w with getCs name w
... | just u = inj₁ (u , refl)
... | nothing = inj₂ refl


mkcs-inj1 : {n1 n2 : Name} {l1 l2 : List Term} {r1 r2 : Res} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → n1 ≡ n2
mkcs-inj1 refl =  refl


mkcs-inj2 : {n1 n2 : Name} {l1 l2 : List Term} {r1 r2 : Res} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → l1 ≡ l2
mkcs-inj2 refl =  refl


mkcs-inj3 : {n1 n2 : Name} {l1 l2 : List Term} {r1 r2 : Res} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → r1 ≡ r2
mkcs-inj3 refl =  refl


getCs-same-name : (name : Name) (w : world) (e : cs)
                  → getCs name w ≡ just e
                  → cs.name e ≡ name
getCs-same-name name (start name₁ res ∷ w) (mkcs n l r) h with name ≟ name₁
... | yes p = sym (mkcs-inj1 (just-inj h))
... | no p = getCs-same-name name w (mkcs n l r) h
getCs-same-name name (choice name₁ t ∷ w) e h = getCs-same-name name w e h




getCs++ : (name : Name) (w w' : world) (l : List Term) (r : Res)
          → getCs name w ≡ just (mkcs name l r)
          → getCs name (w ++ w') ≡ just (mkcs name (l ++ getChoices name w') r)
getCs++ name (start name₁ res ∷ w) w' l r e with name ≟ name₁
... | yes p rewrite getChoices++ name w w' rewrite mkcs-inj2 (just-inj e) rewrite mkcs-inj3 (just-inj e) = refl
... | no p = getCs++ name w w' l r e
getCs++ name (choice name₁ t ∷ w) w' l r e = getCs++ name w w' l r e


getCs++-same-choice : (name : Name) (w : world) (l : List Term) (r : Res) (t : Term)
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name t ]) ≡ just (mkcs name (l ++ [ t ]) r)
getCs++-same-choice name w l r t e rewrite getCs++ name w [ choice name t ] l r e with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)


getCs++-diff-choice : (name name₁ : Name) (w : world) (l : List Term) (r : Res) (t : Term)
                      → ¬ name ≡ name₁
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name₁ t ]) ≡ just (mkcs name l r)
getCs++-diff-choice name name₁ w l r t d e rewrite getCs++ name w [ choice name₁ t ] l r e with name ≟ name₁
... | yes p = ⊥-elim (d p)
... | no p rewrite ++[] l = refl


≽-pres-getCs : {w1 w2 : world} {name : Name} {l : List Term} {r : Res}
                 → w2 ≽ w1
                 → getCs name w1 ≡ just (mkcs name l r)
                 → Σ (List Term) (λ l' → getCs name w2 ≡ just (mkcs name (l ++ l') r))
≽-pres-getCs {w1} {.w1} {name} {l} {r} (extRefl .w1) i =
  ([] , subst (λ x → getCs name w1 ≡ just (mkcs name x r)) (sym (++[] l)) i)
≽-pres-getCs {w1} {w2} {name} {l} {r} (extTrans ext ext₁) i =
  let (l1 , i1) = ≽-pres-getCs ext₁ i in
  let (l2 , i2) = ≽-pres-getCs ext i1 in
  (l1 ++ l2 , subst (λ x → getCs name w2 ≡ just (mkcs name x r)) (++-assoc l l1 l2) i2)
≽-pres-getCs {w1} {.(w1 ++ choice name₁ t ∷ [])} {name} {l} {r} (extChoice .w1 name₁ l₁ t res x x₁) i with name ≟ name₁
... | yes p rewrite p = ([ t ] , getCs++-same-choice name₁ w1 l r t i)
... | no p rewrite getCs++-diff-choice name name₁ w1 l r t p i =
  ([] , subst (λ x → just (mkcs name l r) ≡ just (mkcs name x r)) (sym (++[] l)) refl)
≽-pres-getCs {w1} {.(w1 ++ start name₁ res ∷ [])} {name} {l} {r} (extEntry .w1 name₁ res x) i rewrite getCs++ name w1 [ start name₁ res ] l r i =
  ([] , refl)


wdom++ : (w₁ w₂ : 𝕎·) → wdom (w₁ ++ w₂) ≡ wdom w₁ ++ wdom w₂
wdom++ [] w₂ = refl
wdom++ (start name res ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl
wdom++ (choice name t ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl


wdomAddChoice : (w : 𝕎·) (name : Name) (t : Term) → wdom (w ∷ʳ choice name t) ≡ wdom w
wdomAddChoice w name t rewrite wdom++ w [ choice name t ] rewrite ++[] (wdom w) = refl


wdomAddStart : (w : 𝕎·) (name : Name) (r : Res) → wdom (w ∷ʳ start name r) ≡ wdom w ∷ʳ name
wdomAddStart w name r rewrite wdom++ w [ start name r ] = refl


extwPreservesNorepeats : (w1 w2 : 𝕎·) → w2 ≽ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extwPreservesNorepeats w1 .w1 (extRefl .w1) norep = norep
extwPreservesNorepeats w1 w2 (extTrans e e₁) norep = extwPreservesNorepeats _ _ e (extwPreservesNorepeats _ _ e₁ norep)
extwPreservesNorepeats w1 .(w1 ++ choice name t ∷ []) (extChoice .w1 name l t res x x₁) norep rewrite wdomAddChoice w1 name t = norep
extwPreservesNorepeats w1 .(w1 ++ start name res ∷ []) (extEntry .w1 name res x) norep rewrite wdomAddStart w1 name res =
  norepeats∷ʳ _ _ norep x


≽-pres-∈world : {w1 w2 : 𝕎·} {name : Name} {l : List Term} {r : Res}
                  → w2 ≽ w1
                  → ∈world (mkcs name l r) w1
                  → Σ (List Term) (λ l' → ∈world (mkcs name (l ++ l') r) w2)
≽-pres-∈world {w1} {.w1} {name} {l} {r} (extRefl .w1) i =
  ([] , subst (λ x → ∈world (mkcs name x r) w1) (sym (++[] l)) i)
≽-pres-∈world {w1} {w2} {name} {l} {r} (extTrans e e₁) i =
  let (l1 , i1) = ≽-pres-∈world e₁ i in
  let (l2 , i2) = ≽-pres-∈world e i1 in
  (l1 ++ l2 , subst (λ x → ∈world (mkcs name x r) w2) (++-assoc l l1 l2) i2)
≽-pres-∈world {w1} {.(w1 ++ choice name₁ t ∷ [])} {name} {l} {r} (extChoice .w1 name₁ l₁ t res x x₁) i with name ≟ name₁
... | yes p rewrite p = ([ t ] , getCs++-same-choice name₁ w1 l r t i)
... | no p rewrite getCs++-diff-choice name name₁ w1 l r t p i =
  ([] , subst (λ x → just (mkcs name l r) ≡ just (mkcs name x r)) (sym (++[] l)) refl)
≽-pres-∈world {w1} {.(w1 ++ start name₁ res ∷ [])} {name} {l} {r} (extEntry .w1 name₁ res x) i rewrite getCs++ name w1 [ start name₁ res ] l r i =
  ([] , refl)


∈world-extcs : (w : 𝕎·) (name : Name) (l : List Term) (r : Res) (t : Term)
               → ∈world (mkcs name l r) w
               → ∈world (mkcs name (l ∷ʳ t) r) (extcs w name t)
∈world-extcs w name l r t i rewrite getCs++ name w [ choice name t ] l r i with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)


getCs++∉ : (name : Name) (w w' : 𝕎·)
          → getCs name w ≡ nothing
          → getCs name (w ++ w') ≡ getCs name w'
getCs++∉ name [] w' h = refl
getCs++∉ name (start name₁ res ∷ w) w' h with name ≟ name₁
getCs++∉ name (start name₁ res ∷ w) w' () | yes p
... | no p = getCs++∉ name w w' h
getCs++∉ name (choice name₁ t ∷ w) w' h = getCs++∉ name w w' h


∉-getCs-nothing : (w : 𝕎·) (name : Name) → ¬ (name ∈ (wdom w)) → getCs name w ≡ nothing
∉-getCs-nothing [] name i = refl
∉-getCs-nothing (start name₁ res ∷ w) name i with name ≟ name₁
... | yes p rewrite p = ⊥-elim (i (here refl))
... | no p = ∉-getCs-nothing w name λ j → i (there j)
∉-getCs-nothing (choice name₁ t ∷ w) name i = ∉-getCs-nothing w name i


∈world-newcs : (w : 𝕎·) (name : Name) (r : Res)
               → ¬ (name ∈ (wdom w))
               → ∈world (mkcs name [] r) (newcs w name r)
∈world-newcs w name r ni rewrite getCs++∉ name w [ start name r ] (∉-getCs-nothing w name ni) with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)




-- ####### choice instance

-- We now define an instance of CsChoice
-- similar to lookup
getCsChoice : (n : ℕ) (name : Name) (w : world) → Maybe Term
getCsChoice n name w with getCs name w
... | just (mkcs _ l _) = select n l
... | nothing = nothing


newCsChoice : (w : 𝕎·) → Name
newCsChoice w = fst (freshName (wdom w))


startCsChoice : (cs : Name) (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
startCsChoice cs r w = newcs w cs r


startNewCsChoice : (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
startNewCsChoice r w = startCsChoice (newCsChoice w) r w


getCs-newcs : (w : 𝕎·) (name : Name) (r : Res)
              → ¬ (name ∈ wdom w)
              → getCs name (newcs w name r) ≡ just (mkcs name [] r)
getCs-newcs [] name r ni with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)
getCs-newcs (start name₁ res ∷ w) name r ni with name ≟ name₁
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = getCs-newcs w name r (λ x → ni (there x))
getCs-newcs (choice name₁ t ∷ w) name r ni = getCs-newcs w name r ni


getCsChoice-startNewCsChoice-aux : (n : ℕ) (r : Res) (w : 𝕎·) (name : Name)
                                   → ¬ (name ∈ wdom w)
                                   → getCsChoice n name (startCsChoice name r w) ≡ nothing
getCsChoice-startNewCsChoice-aux n r w name ni rewrite getCs-newcs w name r ni = refl


getCsChoice-startNewCsChoice : (n : ℕ) (r : Res) (w : 𝕎·)
                               → getCsChoice n (newCsChoice w) (startNewCsChoice r w) ≡ nothing
getCsChoice-startNewCsChoice n r w = getCsChoice-startNewCsChoice-aux n r w (newCsChoice w) (snd (freshName (wdom w)))


¬≡startNewCsChoice : (name : Name) (r : Res) (w : world) → ¬ w ≡ startCsChoice name r w
¬≡startNewCsChoice name r (x ∷ w) e = ¬≡startNewCsChoice name r w (snd (∷-injective e))


startNewCsChoice⊏ : (r : Res) (w : 𝕎·) → w ⊏ startNewCsChoice r w
startNewCsChoice⊏ r w =
  (extEntry w (newCsChoice w) r (snd (freshName (wdom w)))) ,
  ¬≡startNewCsChoice (newCsChoice w) r w



defRes : Res
defRes n t = ⊥


getRes : Name → world → Res
getRes name [] = defRes
getRes name (start n r ∷ w) with name ≟ n
... | yes p = r
... | no p = getRes name w
getRes name (choice _ _ ∷ w) = getRes name w


data ≺cs : cs → cs → Set₁ where
  ≺CS : (c : Name) (l l' : List Term) (r : Res)
        → 0 < length l'
        → ≺cs (mkcs c l r) (mkcs c (l ++ l') r)


progressCs : (c : Name) (w1 w2 : 𝕎·) → Set₁
progressCs c w1 w2 = Σ cs (λ e1 → Σ cs (λ e2 → ∈world e1 w1 × ∈world e2 w2 × ≺cs e1 e2))


compatibleRes : (r1 r2 : Res{0ℓ}) → Set
compatibleRes r1 r2 =
  (n : ℕ) (t : Term) → (r1 n t → r2 n t) × (r2 n t → r1 n t)


compatibleCs : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set₁
compatibleCs c w r = Σ (List Term) (λ l → ∈world (mkcs c l r) w)
-- Lift 1ℓ (compatibleRes r (getRes c w))


compatibleRes-refl : (r : Res) → compatibleRes r r
compatibleRes-refl r n t = (λ x → x) , λ x → x


getRes-newcs : (c : Name) (r : Res) (w : 𝕎·)
               → ¬ (c ∈ wdom w)
               → getRes c (newcs w c r) ≡ r
getRes-newcs c r [] ni with c ≟ c
... | yes p = refl
... | no p = ⊥-elim (p refl)
getRes-newcs c r (start name res ∷ w) ni with c ≟ name
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = getRes-newcs c r w λ x → ni (there x)
getRes-newcs c r (choice name t ∷ w) ni = getRes-newcs c r w ni



{--
getChoices-newcs : (c : Name) (r : Res) (w : 𝕎·)
                   → ¬ (c ∈ wdom w)
                   → getChoices c (newcs w c r) ≡ []
getChoices-newcs c r [] ni with c ≟ c
... | yes p = refl
... | no p = ⊥-elim (p refl)
getChoices-newcs c r (start name res ∷ w) ni = getChoices-newcs c r w (λ x → ni (there x))
getChoices-newcs c r (choice name t ∷ w) ni with c ≟ name
... | yes p rewrite p = {!!}
... | no p = getChoices-newcs c r w ni
--}


startCsChoiceCompatible : (r : Res{0ℓ}) (w : 𝕎·) → compatibleCs (newCsChoice w) (startNewCsChoice r w) r
startCsChoiceCompatible r w rewrite getCs-newcs w (newCsChoice w) r (snd (freshName (wdom w))) = [] , refl


freezeCs : (c : Name) (w : 𝕎·) (t : Term) → 𝕎·
freezeCs c w t = extcs w c t



¬≡freezeCs : (c : Name) (w : world) (t : Term) → ¬ w ≡ freezeCs c w t
¬≡freezeCs c [] t ()
¬≡freezeCs c (x ∷ w) t e = ¬≡freezeCs c w t (snd (∷-injective e))


getCs→∈world : {c : Name} {r : Res} {w : 𝕎·} {l : List Term} → getCs c w ≡ just (mkcs c l r) → ∈world (mkcs c l r) w
getCs→∈world {c} {r} {w} {l} h rewrite h = refl


freezeCs⊑ : (c : Name) (w : 𝕎·) (t : Term) {r : Res} → compatibleCs c w r → ((n : ℕ) → r n t) → w ⊑· freezeCs c w t
freezeCs⊑ c w t {r} (l , comp) rt with getCs⊎ c w
... | inj₁ (u , p) rewrite p | just-inj comp =
  extChoice w c l t r (getCs→∈world {c} {r} {w} p) (rt (length l)) --, ¬≡freezeCs c w t
... | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym comp))



getChoiceΣ : (k : ℕ) (name : Name) (w : world) (t : Term)
             → getCsChoice k name w ≡ just t
             → Σ (List Term) (λ l → Σ Res (λ r → getCs name w ≡ just (mkcs name l r) × select k l ≡ just t))
getChoiceΣ k name w t gc with getCs⊎ name w
... | inj₁ (mkcs n l r , p) rewrite p | getCs-same-name name w (mkcs n l r) p = (l , r , refl , gc)
getChoiceΣ k name w t gc | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym gc))



≽-pres-getChoice : {w1 w2 : world} {k : ℕ} {name : Name} {t : Term}
                   → w2 ≽ w1
                   → getCsChoice k name w1 ≡ just t
                   → getCsChoice k name w2 ≡ just t
≽-pres-getChoice {w1} {w2} {k} {name} {t} ext gc = gc3
  where
    h : Σ (List Term) (λ l → Σ Res (λ r → getCs name w1 ≡ just (mkcs name l r) × select k l ≡ just t))
    h = getChoiceΣ k name w1 t gc

    l : List Term
    l = proj₁ h

    r : Res
    r = proj₁ (proj₂ h)

    gc1 : getCs name w1 ≡ just (mkcs name l r)
    gc1 = proj₁ (proj₂ (proj₂ h))

    sel : select k l ≡ just t
    sel = proj₂ (proj₂ (proj₂ h))

    q : Σ (List Term) (λ l' → getCs name w2 ≡ just (mkcs name (l ++ l') r))
    q = ≽-pres-getCs ext gc1

    l' : List Term
    l' = proj₁ q

    gc2 : getCs name w2 ≡ just (mkcs name (l ++ l') r)
    gc2 = proj₂ q

    gc3 : getCsChoice k name w2 ≡ just t
    gc3 rewrite gc2 = select++-just {Term} {k} {l} {l'} sel



getFreezeCs : (c : Name) (w : 𝕎·) (t : Term) {r : Res{0ℓ}}
              → compatibleCs c w r
              → Σ ℕ (λ n → ∀𝕎 (freezeCs c w t) (λ w' _ → Lift 2ℓ (getCsChoice n c w' ≡ just t)))
getFreezeCs c w t {r} (l , comp) =
  length l , aw
  where
    aw : ∀𝕎 (freezeCs c w t) (λ w' _ → Lift 2ℓ (getCsChoice (length l) c w' ≡ just t))
    aw w1 e1 = lift (≽-pres-getChoice e1 g)
      where
        g : getCsChoice (length l) c (freezeCs c w t) ≡ just t
        g rewrite getCs++-same-choice c w l r t comp | select-last l t = refl



open import choice(PossibleWorldsCS)

csChoice : Choice
csChoice =
  mkChoice
    getCsChoice
    newCsChoice
    startCsChoice
    getCsChoice-startNewCsChoice
    startNewCsChoice⊏
    compatibleCs
    progressCs
    startCsChoiceCompatible
    freezeCs
    freezeCs⊑
    getFreezeCs
-- ≽-pres-getChoice

open import choiceDef(PossibleWorldsCS)(csChoice)


getChoice-extcs-last : (w : 𝕎·) (k : ℕ) (name : Name) (l : List Term) (r : Res) (t : Term)
                       → k ≡ length l
                       → getCs name w ≡ just (mkcs name l r)
                       → getChoice· k name (extcs w name t) ≡ just t
getChoice-extcs-last w k name l r t e h rewrite e | getCs++ name w [ choice name t ] l r h with name ≟ name
... | yes p = select-last l t
... | no p = ⊥-elim (p refl)


≽-ΣgetChoice : (w1 w2 : 𝕎·) (name : Name) (l1 l2 : List Term) (r : Res) (k : ℕ)
               → ∈world (mkcs name l1 r) w1
               → ∈world (mkcs name l2 r) w2
               → length l1 ≤ k
               → k < length l2
               → w2 ≽ w1
               → Σ Term (λ t → Σ world (λ w → Σ (List Term) (λ l →
                     getChoice· k name (extcs w name t) ≡ just t
                   × ∈world (mkcs name l r) w
                   × k ≡ length l
                   × w2 ≽ (extcs w name t)
                   × w ≽ w1
                   × r k t)))
≽-ΣgetChoice w1 .w1 name l1 l2 r k i1 i2 len1 len2 (extRefl .w1)
  rewrite i1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 w2 name l1 l2 r k i1 i2 len1 len2 (extTrans {w1} {w3} {w2} ext ext₁) with ≽-pres-∈world ext₁ i1
... | (l , iw) with k <? length (l1 ++ l)
...            | yes p =
  let (t , w , l0 , h1 , h2 , h3 , h4 , h5 , h6) = ≽-ΣgetChoice w1 w3 name l1 (l1 ++ l) r k i1 iw len1 p ext₁ in
  (t , w , l0 , h1 , h2 , h3 , extTrans ext h4 , h5 , h6)
...            | no p =
  let (t , w , l0 , h1 , h2 , h3 , h4 , h5 , h6) = ≽-ΣgetChoice w3 w2 name (l1 ++ l) l2 r k iw i2 (≮⇒≥ p) len2 ext in
  (t , w , l0 , h1 , h2 , h3 , h4 , extTrans h5 ext₁ , h6)
≽-ΣgetChoice w1 .(w1 ++ choice name₁ t ∷ []) name l1 l2 r k i1 i2 len1 len2 (extChoice .w1 name₁ l t res x x₁) with name ≟ name₁
... | yes p rewrite p | x | sym (mkcs-inj2 (just-inj i1))
                    | sym (mkcs-inj3 (just-inj i1))
                    | getCs++ name₁ w1 [ choice name₁ t ] l res x
                    | sym (mkcs-inj2 (just-inj i2))
            with name₁ ≟ name₁
...         | yes q rewrite length-++ l {[ t ]} | +-comm (length l) 1 =
              let len : k ≡ length l
                  len = ≤-s≤s-≡ _ _ len1 len2 in
                  (t , w1 , l , getChoice-extcs-last w1 k name₁ l res t len x ,
                    x , len , extRefl (extcs w1 name₁ t) , extRefl w1 , subst (λ x → res x t) (sym len) x₁)
...         | no q rewrite ++[] l = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 .(w1 ++ choice name₁ t ∷ []) name l1 l2 r k i1 i2 len1 len2 (extChoice .w1 name₁ l t res x x₁)
    | no p rewrite getCs++ name w1 [ choice name₁ t ] l1 r i1
           with name ≟ name₁
...        | yes q = ⊥-elim (p q)
...        | no q rewrite ++[] l1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 .(w1 ++ start name₁ res ∷ []) name l1 l2 r k i1 i2 len1 len2 (extEntry .w1 name₁ res x) with name ≟ name₁
... | yes p rewrite p | getCs++ name₁ w1 [ start name₁ res ] l1 r i1 | ++[] l1 | sym (mkcs-inj2 (just-inj i2)) =
  ⊥-elim (1+n≰n (≤-trans len2 len1))
... | no p rewrite getCs++ name w1 [ start name₁ res ] l1 r i1 | ++[] l1 | sym (mkcs-inj2 (just-inj i2)) =
  ⊥-elim (1+n≰n (≤-trans len2 len1))
\end{code}
