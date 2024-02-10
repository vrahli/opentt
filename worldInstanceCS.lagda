\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
--open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
--open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
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


module worldInstanceCS (E : Extensionality 0ℓ 0ℓ)  where
\end{code}



This provides an instance of world and choice for choice sequences


\begin{code}
open import choice

choiceCS : Choice
choiceCS = mkChoice ℕ (λ x → #NUM x) (λ c → refl) λ c → refl --(λ {a} {b} x → x)

open import choiceDef{1ℓ}(choiceCS)



record cs : Set₁ where
  constructor mkcs
  field
    name    : Name
    choices : List ℂ·
    res     : Res{0ℓ}


data entry : Set₁ where
  start  : (name : Name) (res : Res) → entry
  choice : (name : Name) (t : ℂ·) → entry


-- Worlds - entries are added at the end of the list
world : Set₁
world = List entry


getChoices : Name → world → List ℂ·
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


wnames : world → List Name
wnames [] = []
wnames (start _ _ ∷ w) = wnames w
wnames (choice _ t ∷ w) = names ⌜ #NUM t ⌝ ++ wnames w


remNRes : {L : Level} (n : Name) (l : List (NRes{L})) → List (NRes{L})
remNRes {L} n [] = []
remNRes {L} n (r ∷ l) with n ≟ NRes.name r
... | yes p = remNRes n l
... | no p = r ∷ remNRes n l


wrdom : world → List NRes
wrdom [] = []
wrdom (start name r ∷ w) = mkNRes name r ∷ remNRes name (wrdom w)
wrdom (choice _ _ ∷ w) = wrdom w


∈world : cs → world → Set₁
∈world e w = getCs (cs.name e) w ≡ just e


newcs : world → Name → Res → world
newcs w name r = w ∷ʳ start name r


extcs : world → Name → ℂ· → world
extcs w name t = w ∷ʳ choice name t


-- w2 extends w1
data _≽_ : (w2 : world) (w1 : world) → Set₁ where
  extRefl : (w : world) → w ≽ w
  extTrans : {w1 w2 w3 : world} → w3 ≽ w2 → w2 ≽ w1 → w3 ≽ w1
  extChoice :
    (w : world) (name : Name) (l : List ℂ·) (t : ℂ·) (res : Res)
    → ∈world (mkcs name l res) w
    → ·ᵣ res (length l) t
    → (extcs w name t) ≽ w
  extEntry :
    (w : world) (name : Name) (res : Res)
    → ¬ (name ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → (newcs w name res) ≽ w



open import world

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


mkcs-inj1 : {n1 n2 : Name} {l1 l2 : List ℂ·} {r1 r2 : Res} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → n1 ≡ n2
mkcs-inj1 refl =  refl


mkcs-inj2 : {n1 n2 : Name} {l1 l2 : List ℂ·} {r1 r2 : Res} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → l1 ≡ l2
mkcs-inj2 refl =  refl


mkcs-inj3 : {n1 n2 : Name} {l1 l2 : List ℂ·} {r1 r2 : Res} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → r1 ≡ r2
mkcs-inj3 refl =  refl


getCs-same-name : (name : Name) (w : world) (e : cs)
                  → getCs name w ≡ just e
                  → cs.name e ≡ name
getCs-same-name name (start name₁ res ∷ w) (mkcs n l r) h with name ≟ name₁
... | yes p = sym (mkcs-inj1 (just-inj h))
... | no p = getCs-same-name name w (mkcs n l r) h
getCs-same-name name (choice name₁ t ∷ w) e h = getCs-same-name name w e h




getCs++ : (name : Name) (w w' : world) (l : List ℂ·) (r : Res)
          → getCs name w ≡ just (mkcs name l r)
          → getCs name (w ++ w') ≡ just (mkcs name (l ++ getChoices name w') r)
getCs++ name (start name₁ res ∷ w) w' l r e with name ≟ name₁
... | yes p rewrite getChoices++ name w w' | mkcs-inj2 (just-inj e) | mkcs-inj3 (just-inj e) = refl
... | no p = getCs++ name w w' l r e
getCs++ name (choice name₁ t ∷ w) w' l r e = getCs++ name w w' l r e


getCs++-same-choice : (name : Name) (w : world) (l : List ℂ·) (r : Res) (t : ℂ·)
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name t ]) ≡ just (mkcs name (l ++ [ t ]) r)
getCs++-same-choice name w l r t e rewrite getCs++ name w [ choice name t ] l r e with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)


getCs++-diff-choice : (name name₁ : Name) (w : world) (l : List ℂ·) (r : Res) (t : ℂ·)
                      → ¬ name ≡ name₁
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name₁ t ]) ≡ just (mkcs name l r)
getCs++-diff-choice name name₁ w l r t d e rewrite getCs++ name w [ choice name₁ t ] l r e with name ≟ name₁
... | yes p = ⊥-elim (d p)
... | no p rewrite ++[] l = refl



resSatCs : (n : ℕ) (l : List ℂ·) (r : Res{0ℓ}) → Set
resSatCs n [] r = ⊤
resSatCs n (t ∷ l) r = ·ᵣ r n t × resSatCs (suc n) l r


pres-resSatCs : (l l' : List ℂ·) (r : Res{0ℓ}) → Set
pres-resSatCs l l' r = resSatCs 0 l r → resSatCs 0 (l ++ l') r


pres-resSatCs-[] : (l : List ℂ·) (r : Res{0ℓ}) → pres-resSatCs l [] r
pres-resSatCs-[] l r x rewrite ++[] l = x


→resSatCs++ : (n : ℕ) (l1 l2 : List ℂ·) (r : Res{0ℓ})
               → resSatCs n l1 r
               → resSatCs (n + length l1) l2 r
               → resSatCs n (l1 ++ l2) r
→resSatCs++ n [] l2 r sat1 sat2 rewrite +-identityʳ n = sat2
→resSatCs++ n (x ∷ l1) l2 r (cond , sat1) sat2 rewrite +-suc n (length l1) =
  cond , →resSatCs++ (suc n) l1 l2 r sat1 sat2


pres-resSatCs-∷ʳ : (l : List ℂ·) (t : ℂ·) (r : Res{0ℓ}) → ·ᵣ r (length l) t → pres-resSatCs l [ t ] r
pres-resSatCs-∷ʳ l t r c x = →resSatCs++ 0 l [ t ] r x (c , tt)



→pres-resSatCs++ : {l l1 l2 : List ℂ·} {r : Res{0ℓ}}
                    → pres-resSatCs l l1 r
                    → pres-resSatCs (l ++ l1) l2 r
                    → pres-resSatCs l (l1 ++ l2) r
→pres-resSatCs++ {l} {l1} {l2} {r} s1 s2 s rewrite sym (++-assoc l l1 l2) = s2 (s1 s)



≽-pres-getCs : {w1 w2 : world} {name : Name} {l : List ℂ·} {r : Res}
                 → w2 ≽ w1
                 → getCs name w1 ≡ just (mkcs name l r)
                 → Σ (List ℂ·) (λ l' → getCs name w2 ≡ just (mkcs name (l ++ l') r) × pres-resSatCs l l' r)
≽-pres-getCs {w1} {.w1} {name} {l} {r} (extRefl .w1) i =
  [] , subst (λ x → getCs name w1 ≡ just (mkcs name x r)) (sym (++[] l)) i , pres-resSatCs-[] l r
≽-pres-getCs {w1} {w2} {name} {l} {r} (extTrans ext ext₁) i =
  let (l1 , i1 , s1) = ≽-pres-getCs ext₁ i in
  let (l2 , i2 , s2) = ≽-pres-getCs ext i1 in
  l1 ++ l2 , subst (λ x → getCs name w2 ≡ just (mkcs name x r)) (++-assoc l l1 l2) i2 , →pres-resSatCs++ s1 s2
≽-pres-getCs {w1} {.(w1 ++ choice name₁ t ∷ [])} {name} {l} {r} (extChoice .w1 name₁ l₁ t res x x₁) i with name ≟ name₁
... | yes p rewrite p | i | sym (mkcs-inj2 (just-inj x)) | sym (mkcs-inj3 (just-inj x)) =
  [ t ] , getCs++-same-choice name₁ w1 l r t i , pres-resSatCs-∷ʳ l t r x₁
... | no p rewrite getCs++-diff-choice name name₁ w1 l r t p i =
  [] , subst (λ x → just (mkcs name l r) ≡ just (mkcs name x r)) (sym (++[] l)) refl , pres-resSatCs-[] l r
≽-pres-getCs {w1} {.(w1 ++ start name₁ res ∷ [])} {name} {l} {r} (extEntry .w1 name₁ res x) i rewrite getCs++ name w1 [ start name₁ res ] l r i =
  [] , refl , pres-resSatCs-[] l r


wdom++ : (w₁ w₂ : 𝕎·) → wdom (w₁ ++ w₂) ≡ wdom w₁ ++ wdom w₂
wdom++ [] w₂ = refl
wdom++ (start name res ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl
wdom++ (choice name t ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl


wdomAddChoice : (w : 𝕎·) (name : Name) (t : ℂ·) → wdom (w ∷ʳ choice name t) ≡ wdom w
wdomAddChoice w name t rewrite wdom++ w [ choice name t ] rewrite ++[] (wdom w) = refl


wdomAddStart : (w : 𝕎·) (name : Name) (r : Res) → wdom (w ∷ʳ start name r) ≡ wdom w ∷ʳ name
wdomAddStart w name r rewrite wdom++ w [ start name r ] = refl


extwPreservesNorepeats : (w1 w2 : 𝕎·) → w2 ≽ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extwPreservesNorepeats w1 .w1 (extRefl .w1) norep = norep
extwPreservesNorepeats w1 w2 (extTrans e e₁) norep = extwPreservesNorepeats _ _ e (extwPreservesNorepeats _ _ e₁ norep)
extwPreservesNorepeats w1 .(w1 ++ choice name t ∷ []) (extChoice .w1 name l t res x x₁) norep rewrite wdomAddChoice w1 name t = norep
extwPreservesNorepeats w1 .(w1 ++ start name res ∷ []) (extEntry .w1 name res x) norep rewrite wdomAddStart w1 name res =
  norepeats∷ʳ _ _ norep x



≽-pres-∈world : {w1 w2 : 𝕎·} {name : Name} {l : List ℂ·} {r : Res}
                  → w2 ≽ w1
                  → ∈world (mkcs name l r) w1
                  → Σ (List ℂ·) (λ l' → ∈world (mkcs name (l ++ l') r) w2 × pres-resSatCs l l' r)
≽-pres-∈world {w1} {w2} {name} {l} {r} e i = ≽-pres-getCs e i


∈world-extcs : (w : 𝕎·) (name : Name) (l : List ℂ·) (r : Res) (t : ℂ·)
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




preCompatibleCs : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set₁
preCompatibleCs c w r = Σ (List ℂ·) (λ l → ∈world (mkcs c l r) w)


-- This is the same as 'preCompatibleCs' & enforces satisfiability too
compatibleCs : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set₁
compatibleCs c w r = Σ (List ℂ·) (λ l → ∈world (mkcs c l r) w × resSatCs 0 l r)



⊑-compatibleCs : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatibleCs c w1 r → compatibleCs c w2 r
⊑-compatibleCs {c} {w1} {w2} {r} e (l , comp , sat) =
  l ++ (fst (≽-pres-∈world e comp)) ,
  fst (snd (≽-pres-∈world e comp)) ,
  snd (snd (≽-pres-∈world e comp)) sat


compatibleRes-refl : (r : Res{0ℓ}) → compatibleRes r r
compatibleRes-refl r n t = (λ x → x) , λ x → x



open import compatible(PossibleWorldsCS)(choiceCS)

compatibleCS : Compatible
compatibleCS = mkCompatible compatibleCs ⊑-compatibleCs

open import compatibleDef(PossibleWorldsCS)(choiceCS)(compatibleCS)




progressCs : (c : Name) (w1 w2 : 𝕎·) → Set₁
progressCs c w1 w2 =
  (l : List ℂ·) (r : Res)
  → ∈world (mkcs c l r) w1
  → Σ (List ℂ·) (λ l' → ∈world (mkcs c (l ++ l') r) w2 × 0 < length l')



freezeCs : (c : Name) (w : 𝕎·) (t : ℂ·) → 𝕎·
freezeCs c w t = extcs w c t



¬≡freezeCs : (c : Name) (w : world) (t : ℂ·) → ¬ w ≡ freezeCs c w t
¬≡freezeCs c [] t ()
¬≡freezeCs c (x ∷ w) t e = ¬≡freezeCs c w t (snd (∷-injective e))


freezeCsProgress : (c : Name) {w1 w2 : 𝕎·} (t : ℂ·) → w1 ⊑· w2 → progressCs c w1 (freezeCs c w2 t)
freezeCsProgress c {w1} {w2} t e l r i =
  fst (≽-pres-∈world e i) ∷ʳ t ,
  j ,
  k
  where
    j : ∈world (mkcs c (l ++ fst (≽-pres-∈world e i) ∷ʳ t) r) (freezeCs c w2 t)
    j rewrite sym (++-assoc l (fst (≽-pres-∈world e i)) [ t ]) =
      ∈world-extcs w2 c (l ++ (fst (≽-pres-∈world e i))) r t (fst (snd (≽-pres-∈world e i)))

    k : 0 < length (fst (≽-pres-∈world e i) ∷ʳ t)
    k = suc≤len∷ʳ (fst (≽-pres-∈world e i)) t 0 _≤_.z≤n --


freezeDef : NRes{0ℓ} → 𝕎· → 𝕎·
freezeDef r w = freezeCs (NRes.name r) w (Res.def (NRes.res r))


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
compatibleNRes r w = preCompatibleCs (NRes.name r) w (NRes.res r)


⊑→compatibleNRes : {r : NRes} {w1 w2 : 𝕎·} → w1 ⊑· w2 → compatibleNRes r w1 → compatibleNRes r w2
⊑→compatibleNRes {r} {w1} {w2} e (l , comp) =
  l ++ fst (≽-pres-∈world e comp) ,
  fst (snd (≽-pres-∈world e comp))


compatibleListNRes : (l : List NRes) (w : 𝕎·) → Set₁
compatibleListNRes l w = (r : NRes) → r ∈ l → compatibleNRes r w


⊑→compatibleListNRes : {k : List NRes} {w1 w2 : 𝕎·} → w1 ⊑· w2 → compatibleListNRes k w1 → compatibleListNRes k w2
⊑→compatibleListNRes {k} {w1} {w2} e comp r i = ⊑→compatibleNRes e (comp r i)



getCs→∈world : {c : Name} {r : Res} {w : 𝕎·} {l : List ℂ·} → getCs c w ≡ just (mkcs c l r) → ∈world (mkcs c l r) w
getCs→∈world {c} {r} {w} {l} h rewrite h = refl


getCs→∈world' : {c c' : Name} {r : Res} {w : 𝕎·} {l : List ℂ·} → getCs c w ≡ just (mkcs c' l r) → ∈world (mkcs c l r) w
getCs→∈world' {c} {c'} {r} {start name res ∷ w} {l} h with c ≟ name
... | yes p rewrite h | mkcs-inj1 (just-inj h) = refl
... | no p = getCs→∈world' {c} {c'} {r} {w} h
getCs→∈world' {c} {c'} {r} {choice name t ∷ w} {l} h = getCs→∈world' {c} {c'} {r} {w} h



preFreezeCs⊑ : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res} → preCompatibleCs c w r → ⋆ᵣ r t → w ⊑· freezeCs c w t
preFreezeCs⊑ c w t {r} (l , comp) rt with getCs⊎ c w
... | inj₁ (u , p) rewrite p | just-inj comp =
  extChoice w c l t r (getCs→∈world {c} {r} {w} p) (rt (length l)) --, ¬≡freezeCs c w t
... | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym comp))



⊑freezeDef : (r : NRes) (w : 𝕎·) → compatibleNRes r w → w ⊑· freezeDef r w
⊑freezeDef r w comp = preFreezeCs⊑ (NRes.name r) w (Res.def (NRes.res r)) comp (Res.sat (NRes.res r))


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


∈wdom→∈world : {r : NRes} {w : 𝕎·} → r ∈ wrdom w → Σ (List ℂ·) (λ l → ∈world (mkcs (NRes.name r) l (NRes.res r)) w)
∈wdom→∈world {r} {start name res ∷ w} i with NRes.name r ≟ name
... | yes p rewrite (sym p) = getChoices (NRes.name r) w , j
  where
    j : just (mkcs (NRes.name r) (getChoices (NRes.name r) w) res)
        ≡ just (mkcs (NRes.name r) (getChoices (NRes.name r) w) (NRes.res r))
    j rewrite ∈∷remNRes→ {0ℓ} {r} {res} {wrdom w} i = refl
∈wdom→∈world {r} {start name res ∷ w} (here px) | no p = ∈wdom→∈world {r} {w} (⊥-elim (p e))
  where
    e : NRes.name r ≡ name
    e rewrite px = refl
∈wdom→∈world {r} {start name res ∷ w} (there i) | no p = ∈wdom→∈world {r} {w} (∈remNRes→ name i)
∈wdom→∈world {r} {choice name t ∷ w} i =
  fst (∈wdom→∈world {r} {w} i) , j
  where
    j : ∈world (mkcs (NRes.name r) (proj₁ (∈wdom→∈world {r} {w} i)) (NRes.res r)) (choice name t ∷ w)
    j rewrite getCs++∉ (NRes.name r) [ choice name t ] w refl = snd (∈wdom→∈world {r} {w} i)


compatibleListNRes-wrdom : (w : 𝕎·) → compatibleListNRes (wrdom w) w
compatibleListNRes-wrdom w r i = ∈wdom→∈world {r} {w} i


⊑𝕎→seqS : (w : 𝕎·) (n : ℕ) → 𝕎→seq w n ⊑· 𝕎→seq w (suc n)
⊑𝕎→seqS w n = ⊑freezeList (𝕎→seq w n)
                            (wrdom w)
                            (⊑→compatibleListNRes (⊑freezeSeq n (compatibleListNRes-wrdom w)) (compatibleListNRes-wrdom w))


𝕎→csChain : (w : 𝕎·) → chain w
𝕎→csChain w =
  mkChain
    (𝕎→seq w)
    (⊑𝕎→seq0 w)
    (⊑𝕎→seqS w)


NRes-nodup : {L : Level} (l : List (NRes{L})) → Set
NRes-nodup {L} [] = ⊤
NRes-nodup {L} (r ∷ l) = ¬ (NRes.name r ∈ Data.List.map NRes.name l) × NRes-nodup l


¬≡→∈map-remNRes : {L : Level} {name : Name} {x : NRes{L}} {l : List (NRes{L})}
                   → ¬ name ≡ NRes.name x
                   → NRes.name x ∈ Data.List.map NRes.name l
                   → NRes.name x ∈ Data.List.map NRes.name (remNRes name l)
¬≡→∈map-remNRes {L} {name} {x} {x₁ ∷ l} d (here px) with name ≟ NRes.name x₁
... | yes p rewrite p = ⊥-elim (d (sym px))
... | no p = here px
¬≡→∈map-remNRes {L} {name} {x} {x₁ ∷ l} d (there i) with name ≟ NRes.name x₁
... | yes p rewrite p = ¬≡→∈map-remNRes {L} {NRes.name x₁} {x} d i
... | no p = there (¬≡→∈map-remNRes {L} {name} {x} d i)


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


¬∈map-remNRes : {L : Level} (name : Name) (l : List (NRes{L})) → ¬ name ∈ Data.List.map NRes.name (remNRes name l)
¬∈map-remNRes {L} name (x ∷ l) i with name ≟ NRes.name x
... | yes p = ¬∈map-remNRes name l i
¬∈map-remNRes {L} name (x ∷ l) (here px) | no p = p px
¬∈map-remNRes {L} name (x ∷ l) (there i) | no p = ¬∈map-remNRes name l i


NRes-nodup-wdom : (w : 𝕎·) → NRes-nodup (wrdom w)
NRes-nodup-wdom [] = tt
NRes-nodup-wdom (start name res ∷ w) = ¬∈map-remNRes name (wrdom w) , →NRes-nodup-remNRes name (wrdom w) (NRes-nodup-wdom w)
NRes-nodup-wdom (choice name t ∷ w) = NRes-nodup-wdom w


¬≡→≡getCs-extcs : (c name : Name) (w : 𝕎·) (t : ℂ·)
                   → ¬ c ≡ name
                   → getCs c (extcs w name t) ≡ getCs c w
¬≡→≡getCs-extcs c name [] t d = refl
¬≡→≡getCs-extcs c name (start name₁ res ∷ w) t d with c ≟ name₁
... | yes p rewrite p | getChoices++ name₁ w [ choice name t ] with name₁ ≟ name
...                                                               | yes q = ⊥-elim (d q)
...                                                               | no q rewrite ++[] (getChoices name₁ w) = refl
¬≡→≡getCs-extcs c name (start name₁ res ∷ w) t d | no p = ¬≡→≡getCs-extcs c name w t d
¬≡→≡getCs-extcs c name (choice name₁ t₁ ∷ w) t d = ¬≡→≡getCs-extcs c name w t d


¬∈→getCs-freezeList : {c : Name} {k : List NRes} {w : 𝕎·} {e : cs}
                       → ¬ c ∈ Data.List.map NRes.name k
                       → getCs c w ≡ just e
                       → getCs c (freezeList k w) ≡ just e
¬∈→getCs-freezeList {c} {[]} {w} {e} ni z = z
¬∈→getCs-freezeList {c} {x ∷ k} {w} {e} ni z
  rewrite ¬≡→≡getCs-extcs c (NRes.name x) (freezeList k w) (Res.def (NRes.res x)) (λ x → ni (here x)) =
  ¬∈→getCs-freezeList (λ x → ni (there x)) z


getCs-freezeList≡-aux : {L : Level} {c name : Name} {k : List (NRes{L})} {r : Res{L}}
                        → c ≡ name
                        → mkNRes c r ∈ k
                        → name ∈ Data.List.map NRes.name k
getCs-freezeList≡-aux {L} {c} {name} {x ∷ k} {r} e (here px) rewrite e | sym px = here refl
getCs-freezeList≡-aux {L} {c} {name} {x ∷ k} {r} e (there i) = there (getCs-freezeList≡-aux e i)


getCs-freezeList≡ : {c : Name} {r : Res} {k : List NRes} {w : 𝕎·} {l : List ℂ·}
                    → NRes-nodup k
                    → mkNRes c r ∈ k
                    → getCs c w ≡ just (mkcs c l r)
                    → getCs c (freezeList k w) ≡ just (mkcs c (l ∷ʳ Res.def r) r)
getCs-freezeList≡ {c} {r} {x ∷ k} {w} {l} (d , nd) (here px) e rewrite sym px = z2
  where
    z1 : getCs c (freezeList k w) ≡ just (mkcs c l r)
    z1 = ¬∈→getCs-freezeList d e

    z2 : getCs c (freezeList k w ++ choice c (Res.def r) ∷ []) ≡ just (mkcs c (l ++ Res.def r ∷ []) r)
    z2 rewrite getCs++ c (freezeList k w) [ choice c (Res.def r) ] l r z1 with c ≟ c
    ... | yes p = refl
    ... | no p = ⊥-elim (p refl)

getCs-freezeList≡ {c} {r} {x ∷ k} {w} {l} (d , nd) (there i) e
  rewrite ¬≡→≡getCs-extcs c (NRes.name x) (freezeList k w) (Res.def (NRes.res x)) (λ x → d (getCs-freezeList≡-aux x i)) =
  getCs-freezeList≡ nd i e



→∈remNRes : {L : Level} (name : Name) {r : NRes{L}} {l : List (NRes{L})} → ¬ NRes.name r ≡ name  → r ∈ l → r ∈ remNRes name l
→∈remNRes {L} name {r} {x ∷ l} d (here px) with name ≟ NRes.name x
... | yes p rewrite px | p = ⊥-elim (d refl)
... | no p rewrite px = here refl
→∈remNRes {L} name {r} {x ∷ l} d (there i) with name ≟ NRes.name x
... | yes p rewrite p = →∈remNRes (NRes.name x) d i
... | no p = there (→∈remNRes name d i)



getCs→mkNRes∈wrdom : {c : Name} {w : 𝕎·} {l : List ℂ·} {r : Res}
                      → getCs c w ≡ just (mkcs c l r)
                      → mkNRes c r ∈ wrdom w
getCs→mkNRes∈wrdom {c} {start name res ∷ w} {l} {r} e with c ≟ name
... | yes p rewrite p | mkcs-inj1 (just-inj e) | mkcs-inj3 (just-inj e) = here refl
... | no p = there (→∈remNRes name p (getCs→mkNRes∈wrdom {c} {w} e))
getCs→mkNRes∈wrdom {c} {choice name t ∷ w} {l} {r} e = getCs→mkNRes∈wrdom {c} {w} e



wrdom-freezeDef : (w : 𝕎·) (x : NRes) → wrdom (freezeDef x w) ≡ wrdom w
wrdom-freezeDef [] x = refl
wrdom-freezeDef (start name res ∷ w) x rewrite wrdom-freezeDef w x = refl
wrdom-freezeDef (choice name t ∷ w) x = wrdom-freezeDef w x


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


csChainProgress : (w : 𝕎·) (x : Name) (n : ℕ) {r : Res{0ℓ}}
                  → compatibleCs x (chain.seq (𝕎→csChain w) n) r
                  → Σ ℕ (λ m → n < m × progressCs x (chain.seq (𝕎→csChain w) n) (chain.seq (𝕎→csChain w) m))
csChainProgress w x n {r} (l , comp , sat) = suc n , n<1+n n , p
  where
    p : progressCs x (chain.seq (𝕎→csChain w) n) (chain.seq (𝕎→csChain w) (suc n))
    p l' r' i rewrite comp rewrite sym (mkcs-inj2 (just-inj i)) | sym (mkcs-inj3 (just-inj i)) = [ Res.def r ] , e , ≤-refl
      where
        i1 : mkNRes x r ∈ wrdom (freezeSeq (wrdom w) w n)
        i1 = getCs→mkNRes∈wrdom {x} {freezeSeq (wrdom w) w n} comp

        i2 : mkNRes x r ∈ wrdom w
        i2 = ∈wrdom-freezeSeq→ (mkNRes x r) (wrdom w) w n i1

        e : getCs x (freezeList (wrdom w) (freezeSeq (wrdom w) w n)) ≡ just (mkcs x (l ∷ʳ Res.def r) r)
        e = getCs-freezeList≡ {x} {r} {wrdom w} {freezeSeq (wrdom w) w n} {l} (NRes-nodup-wdom w) i2 comp



open import progress(PossibleWorldsCS)(choiceCS)(compatibleCS)

progressCS : Progress
progressCS =
  mkProgress
    progressCs
    𝕎→csChain
    csChainProgress

open import progressDef(PossibleWorldsCS)(choiceCS)(compatibleCS)(progressCS)



-- ####### choice instance

-- We now define an instance of CsChoice
-- similar to lookup
getCsChoice : (n : ℕ) (name : Name) (w : world) → Maybe ℂ·
getCsChoice n name w with getCs name w
... | just (mkcs _ l _) = select n l
... | nothing = nothing



resSatCs-select→·ᵣ : (i : ℕ) {n : ℕ} {r : Res} (l : List ℂ·) {t : ℂ·}
                     → resSatCs i l r
                     → select n l ≡ just t
                     → ·ᵣ r (i + n) t
resSatCs-select→·ᵣ i {0} {r} (x ∷ l) {t} (sat₁ , sat₂) sel rewrite +-comm i 0 | just-inj sel = sat₁
resSatCs-select→·ᵣ i {suc n} {r} (x ∷ l) {t} (sat₁ , sat₂) sel rewrite +-suc i n = resSatCs-select→·ᵣ (suc i) l sat₂ sel


getCsChoiceCompatible : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) (n : ℕ) (t : ℂ·)
                        → compatibleCs c w r → getCsChoice n c w ≡ just t → ·ᵣ r n t
getCsChoiceCompatible c r w n t (l , comp , sat) g rewrite comp = resSatCs-select→·ᵣ 0 l sat g



-- We're really only generating numbers as choices here
T→ℂcs : Term → ℂ·
T→ℂcs (NUM n) = n
T→ℂcs _ = 0


-- only extend if cs's restriction was decidable
chooseCS : (cs : Name) (w : 𝕎·) (c : ℂ·) → 𝕎·
chooseCS n w c with getCs⊎ n w
... | inj₁ (mkcs name l r , e) with Res.dec r
... |    (true , D) with D (length l) c
... |       inj₁ y = extcs w n c
... |       inj₂ y = w
chooseCS n w c | inj₁ (mkcs name l r , e) | (false , _) = w
chooseCS n w c | inj₂ _ = w


chooseCS⊑ : (cs : Name) (w : 𝕎·) (c : ℂ·) → w ⊑· chooseCS cs w c
chooseCS⊑ n w c with getCs⊎ n w
... | inj₁ (mkcs name l r , e) with Res.dec r
... |    (true , D) with D (length l) c
... |       inj₁ y = extChoice w n l c r (getCs→∈world' {n} {name} {r} {w} e) y
... |       inj₂ y = ⊑-refl· _
chooseCS⊑ n w c | inj₁ (mkcs name l r , e) | (false , _) = ⊑-refl· _
chooseCS⊑ n w c | inj₂ _ = ⊑-refl· _


isℂ₀cs : ℂ· → Bool
isℂ₀cs 0 = true
isℂ₀cs _ = false


open import getChoice(PossibleWorldsCS)(choiceCS)(compatibleCS)

getChoiceCS : GetChoice
getChoiceCS = mkGetChoice getCsChoice T→ℂcs chooseCS chooseCS⊑
-- wdom
-- getCsChoiceCompatible

open import getChoiceDef(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)



decℂ₀cs : (c : ℂ·) → c ≡ 0 ⊎ ¬ c ≡ 0
decℂ₀cs 0 = inj₁ refl
decℂ₀cs (suc n) = inj₂ λ ()


decℂ₁cs : (c : ℂ·) → c ≡ 1 ⊎ ¬ c ≡ 1
decℂ₁cs 0 = inj₂ λ ()
decℂ₁cs 1 = inj₁ refl
decℂ₁cs (suc (suc n)) = inj₂ λ ()


open import choiceExt{1ℓ}(PossibleWorldsCS)(choiceCS)

choiceExtCS : ChoiceExt
choiceExtCS = mkChoiceExt 0 1 decℂ₀cs decℂ₁cs

open import choiceExtDef(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)(choiceExtCS)




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


getCsChoice-startCsChoice-nothing : (n : ℕ) (r : Res) (w : 𝕎·) (name : Name)
                                    → ¬ (name ∈ wdom w)
                                    → getCsChoice n name (startCsChoice name r w) ≡ nothing
getCsChoice-startCsChoice-nothing n r w name ni rewrite getCs-newcs w name r ni = refl


getCsChoice-startCsChoice : (n : ℕ) (r : Res) (w : 𝕎·) (t : ℂ·) (name : Name)
                            → ¬ name ∈ wdom w
                            → getCsChoice n name (startCsChoice name r w) ≡ just t → t ≡ Res.def r
getCsChoice-startCsChoice n r w t name ni e rewrite getCsChoice-startCsChoice-nothing n r w name ni
  = ⊥-elim (¬just≡nothing (sym e))


¬≡startNewCsChoice : (name : Name) (r : Res) (w : world) → ¬ w ≡ startCsChoice name r w
¬≡startNewCsChoice name r (x ∷ w) e = ¬≡startNewCsChoice name r w (snd (∷-injective e))


startCsChoice⊏ : (r : Res) (w : 𝕎·) (name : Name) → ¬ name ∈ wdom w → w ⊑· startCsChoice name r w
startCsChoice⊏ r w name ni = extEntry w name r ni


startCsChoiceCompatible : (r : Res{0ℓ}) (w : 𝕎·) (name : Name) → ¬ name ∈ wdom w → compatibleCs name (startCsChoice name r w) r
startCsChoiceCompatible r w name ni rewrite getCs-newcs w name r ni =
  [] , refl , tt



open import newChoice(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)

newChoiceCS : NewChoice
newChoiceCS =
  mkNewChoice
    wdom --newCsChoice
    wnames
    startCsChoice
    getCsChoice-startCsChoice
    startCsChoice⊏
    startCsChoiceCompatible

open import newChoiceDef(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)(newChoiceCS)


open import encoding3(E)


open import computation(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)(choiceExtCS)(newChoiceCS)(enc)


#≠01 : (w : 𝕎·) → ¬ ∼C! w (#NUM 0) (#NUM 1)
#≠01 w h = x (#compVal (∼C!→#⇓ {w} {#NUM 0} {#NUM 1} tt h) tt)
  where
    x : #NUM 0 ≡ #NUM 1 → ⊥
    x ()


ℂ→T→ℂ0 : T→ℂ· ⌜ Cℂ₀ ⌝ ≡ ℂ₀·
ℂ→T→ℂ0 = refl


ℂ→T→ℂ1 : T→ℂ· ⌜ Cℂ₁ ⌝ ≡ ℂ₁·
ℂ→T→ℂ1 = refl


open import choiceVal{1ℓ}(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)(choiceExtCS)(newChoiceCS)(enc)

choiceValCS : ChoiceVal
choiceValCS = mkChoiceVal #≠01 tt tt ℂ→T→ℂ0 ℂ→T→ℂ1

open import choiceValDef(PossibleWorldsCS)(choiceCS)(compatibleCS)(getChoiceCS)(choiceExtCS)(newChoiceCS)(enc)(choiceValCS)


getRes : Name → world → Res
getRes name [] = Res⊤
getRes name (start n r ∷ w) with name ≟ n
... | yes p = r
... | no p = getRes name w
getRes name (choice _ _ ∷ w) = getRes name w


{--
data ≺cs (c : Name) : cs → cs → Set₁ where
  ≺CS : (l l' : List ℂ·) (r : Res)
        → 0 < length l'
        → ≺cs c (mkcs c l r) (mkcs c (l ++ l') r)
--}



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



freezableCs : (c : Name) (w : 𝕎·) → Set
freezableCs c w = ⊤


freezableStartCs : (r : Res{0ℓ}) (w : 𝕎·) → freezableCs (newCsChoice w) (startNewCsChoice r w)
freezableStartCs r w = tt


freezeCs⊑ : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res} → compatibleCs c w r → ⋆ᵣ r t → w ⊑· freezeCs c w t
freezeCs⊑ c w t {r} (l , comp , sat) rt = preFreezeCs⊑ c w t (l , comp) rt



getChoiceΣ : (k : ℕ) (name : Name) (w : world) (t : ℂ·)
             → getCsChoice k name w ≡ just t
             → Σ (List ℂ·) (λ l → Σ Res (λ r → getCs name w ≡ just (mkcs name l r) × select k l ≡ just t))
getChoiceΣ k name w t gc with getCs⊎ name w
... | inj₁ (mkcs n l r , p) rewrite p | getCs-same-name name w (mkcs n l r) p = (l , r , refl , gc)
getChoiceΣ k name w t gc | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym gc))



≽-pres-getChoice : {w1 w2 : world} {k : ℕ} {name : Name} {t : ℂ·}
                   → w2 ≽ w1
                   → getCsChoice k name w1 ≡ just t
                   → getCsChoice k name w2 ≡ just t
≽-pres-getChoice {w1} {w2} {k} {name} {t} ext gc = gc3
  where
    h : Σ (List ℂ·) (λ l → Σ Res (λ r → getCs name w1 ≡ just (mkcs name l r) × select k l ≡ just t))
    h = getChoiceΣ k name w1 t gc

    l : List ℂ·
    l = proj₁ h

    r : Res
    r = proj₁ (proj₂ h)

    gc1 : getCs name w1 ≡ just (mkcs name l r)
    gc1 = proj₁ (proj₂ (proj₂ h))

    sel : select k l ≡ just t
    sel = proj₂ (proj₂ (proj₂ h))

    q : Σ (List ℂ·) (λ l' → getCs name w2 ≡ just (mkcs name (l ++ l') r) × pres-resSatCs l l' r)
    q = ≽-pres-getCs ext gc1

    l' : List ℂ·
    l' = fst q

    gc2 : getCs name w2 ≡ just (mkcs name (l ++ l') r)
    gc2 = fst (snd q)

    gc3 : getCsChoice k name w2 ≡ just t
    gc3 rewrite gc2 = select++-just {0ℓ} {ℂ·} {k} {l} {l'} sel



getFreezeCsAux : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}}
              → compatibleCs c w r
              → Σ ℕ (λ n → ∀𝕎 (freezeCs c w t) (λ w' _ → Lift 2ℓ (getCsChoice n c w' ≡ just t)))
getFreezeCsAux c w t {r} (l , comp , sat) =
  length l , aw
  where
    aw : ∀𝕎 (freezeCs c w t) (λ w' _ → Lift 2ℓ (getCsChoice (length l) c w' ≡ just t))
    aw w1 e1 = lift (≽-pres-getChoice e1 g)
      where
        g : getCsChoice (length l) c (freezeCs c w t) ≡ just t
        g rewrite getCs++-same-choice c w l r t comp | select-last l t = refl



-- We could make use of Rfrz? as we did in worldInstanceRef
getFreezeCs : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}}
              → compatibleCs c w r
              → Rfrz? r
              → freezableCs c w
              → Σ ℕ (λ n → ∀𝕎 (freezeCs c w t) (λ w' _ → Lift 2ℓ (getCsChoice n c w' ≡ just t)))
getFreezeCs c w t {r} compat frz fb = getFreezeCsAux c w t {r} compat


open import freeze(PossibleWorldsCS)(choiceCS)(compatibleCS)(progressCS)(getChoiceCS)(newChoiceCS)

freezeCS : Freeze
freezeCS =
  mkFreeze
--    compatibleCs
--    ⊑-compatibleCs
--    startCsChoiceCompatible
--    getCsChoiceCompatible
    freezeCs
    freezableCs
    freezeCs⊑
    getFreezeCs
    freezableStartCs
    --freezeCsProgress

open import freezeDef(PossibleWorldsCS)(choiceCS)(compatibleCS)(progressCS)(getChoiceCS)(newChoiceCS)(freezeCS)


getChoice-extcs-last : (w : 𝕎·) (k : ℕ) (name : Name) (l : List ℂ·) (r : Res) (t : ℂ·)
                       → k ≡ length l
                       → getCs name w ≡ just (mkcs name l r)
                       → getChoice· k name (extcs w name t) ≡ just t
getChoice-extcs-last w k name l r t e h rewrite e | getCs++ name w [ choice name t ] l r h with name ≟ name
... | yes p = select-last l t
... | no p = ⊥-elim (p refl)


≽-ΣgetChoice : (w1 w2 : 𝕎·) (name : Name) (l1 l2 : List ℂ·) (r : Res) (k : ℕ)
               → ∈world (mkcs name l1 r) w1
               → ∈world (mkcs name l2 r) w2
               → length l1 ≤ k
               → k < length l2
               → w2 ≽ w1
               → Σ ℂ· (λ t → Σ world (λ w → Σ (List ℂ·) (λ l →
                     getChoice· k name (extcs w name t) ≡ just t
                   × ∈world (mkcs name l r) w
                   × k ≡ length l
                   × w2 ≽ (extcs w name t)
                   × w ≽ w1
                   × ·ᵣ r k t)))
≽-ΣgetChoice w1 .w1 name l1 l2 r k i1 i2 len1 len2 (extRefl .w1)
  rewrite i1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 w2 name l1 l2 r k i1 i2 len1 len2 (extTrans {w1} {w3} {w2} ext ext₁) with ≽-pres-∈world ext₁ i1
... | (l , iw , pres) with k <? length (l1 ++ l)
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
                    x , len , extRefl (extcs w1 name₁ t) , extRefl w1 , subst (λ x → ·ᵣ res x t) (sym len) x₁)
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
