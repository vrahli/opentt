{-# OPTIONS --allow-unsolved-metas #-}

\begin{code}
module world where

open import Level using (0ℓ) renaming (suc to lsuc)
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
open import calculus
\end{code}



We first postulate and define enough about worlds to interpret OpenTT
w.r.t. open bars.


\begin{code}
restriction : Set
restriction = (n : ℕ) → Term → Term

record cs : Set where
  constructor mkcs
  field
    name    : csName
    choices : List Term
    res     : restriction

data entry : Set where
  start  : (name : csName) (res : restriction) → entry
  choice : (name : csName) (t : Term) → entry

-- Worlds - entries are added at the end of the list
world : Set
world = List entry

getChoices : csName → world → List Term
getChoices name [] = []
getChoices name (start _ _ ∷ w) = getChoices name w
getChoices name (choice n t ∷ w) with name ≟ n
... | yes p = t ∷ getChoices name w
... | no p = getChoices name w

-- ⟨_⟩_≽_ guarantees that there is only one 'start' for each choice sequence
getCs : csName → world → Maybe cs
getCs name [] = nothing
getCs name (start n r ∷ w) with name ≟ n
... | yes p = just (mkcs name (getChoices name w) r)
... | no p = getCs name w
getCs name (choice n t ∷ w) = getCs name w

wdom : world → List csName
wdom [] = []
wdom (start name _ ∷ w) = name ∷ wdom w
wdom (choice _ _ ∷ w) = wdom w

InhT : Set₁
InhT = (t : Term) → Set

InhW : Set₁
InhW = (w : world) → InhT

InhF : ℕ → Set₁
InhF n = (j : ℕ) → j ≤ n → InhW

record Inh : Set₁ where
  constructor mkinh
  field
    m : ℕ
    n : ℕ
    f : InhF n
--Inh = Σ ℕ (λ m → Σ ℕ (λ n → InhF n))

wfInh≤ : (I : Inh) → Set
wfInh≤ I = Inh.m I ≤ Inh.n I

wfInh< : (I : Inh) → Set
wfInh< I = Inh.m I < Inh.n I

lowerInhF : {n : ℕ} → InhF n → InhF (pred n)
lowerInhF {0} f = f
lowerInhF {suc n} f = λ j c → f j (≤-trans c (n≤1+n _))

-- goes from interval s(m)--s(n) to interval m--n
lower : Inh → Inh
lower (mkinh m n f) = mkinh m (pred n) (lowerInhF f)

-- goes from interval m--s(n) to interval m--n
shrink : Inh → Inh
shrink (mkinh m n f) = mkinh m (pred n) (lowerInhF f)

lift : restriction → restriction
lift res n t = res (suc n) t

{--wfChoices : InhT → List Term → restriction → Set
wfChoices I [] res = ⊤
wfChoices I (t ∷ ts) res = I (res 0 t) × wfChoices I ts (lift res)

wfEntry : InhT → entry → Set
wfEntry I (mkentry name choices res) = wfChoices I choices res

wfWorld : InhT → world → Set
wfWorld I [] = ⊤
wfWorld I (entry ∷ entries) = wfEntry I entry × wfWorld I entries
--}

∈world : cs → world → Set
∈world e w = getCs (cs.name e) w ≡ just e

newcs : world → csName → restriction → world
newcs w name r = w ∷ʳ start name r

extcs : world → csName → Term → world
extcs w name t = w ∷ʳ choice name t

allIW : (I : Inh) (g : InhW → Set) → Set
allIW I g = (j : ℕ) (c₁ : Inh.m I ≤ j) (c₂ : j ≤ Inh.n I) → g (Inh.f I j c₂)

allI : (I : Inh) (g : Inh → Set) → Set
allI I g = (j : ℕ) (c₁ : Inh.m I ≤ j) (c₂ : j ≤ Inh.n I) → g (mkinh (Inh.m I) j (λ i c → Inh.f I i (≤-trans c c₂)))

allI≤ : (I : Inh) (g : (j : ℕ) (c₁ : Inh.m I ≤ j) (c₂ : j ≤ Inh.n I) → Inh → Set) → Set
allI≤ I g = (j : ℕ) (c₁ : Inh.m I ≤ j) (c₂ : j ≤ Inh.n I) → g j c₁ c₂ (mkinh (Inh.m I) j (λ i c → Inh.f I i (≤-trans c c₂)))

-- w2 extends w1
data ⟨_⟩_⪰_ (I : Inh) : (w2 : world) (w1 : world) → Set where
  extRefl : (w : world) → ⟨ I ⟩ w ⪰ w
  extTrans : {w1 w2 w3 : world} → ⟨ I ⟩ w3 ⪰ w2 → ⟨ I ⟩ w2 ⪰ w1 → ⟨ I ⟩ w3 ⪰ w1
  extChoice :
    (w : world) (name : csName) (l : List Term) (t : Term) (res : restriction)
    → ∈world (mkcs name l res) w
    → allIW I (λ i → i w (res (length l) t))
    → ⟨ I ⟩ (extcs w name t) ⪰ w
  extEntry :
    (w : world) (name : csName) (res : restriction)
    → ¬ (name ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → ⟨ I ⟩ (newcs w name res) ⪰ w


{--topInh : (I : Inh) → InhW
topInh (m , n , f) = f n ≤-refl--}


-- w2 extends w1
[_]_⪰_ : (I : Inh) (w2 : world) (w1 : world) → Set
[ I ] w2 ⪰ w1 = ⟨ I ⟩ w2 ⪰ w1

lower-pres-allIW : (I : Inh) (g : InhW → Set) → allIW I g → allIW (lower I) g
lower-pres-allIW (mkinh m 0 f) g h i c₁ c₂ = h i c₁ c₂
lower-pres-allIW (mkinh m (suc n) f) g h i c₁ c₂ = h i c₁ (≤-trans c₂ (n≤1+n _))

lower-pres-⟨⟩≽ : (I : Inh) (w2 w1 : world) → ⟨ I ⟩ w2 ⪰ w1 → ⟨ lower I ⟩ w2 ⪰ w1
lower-pres-⟨⟩≽ I w2 .w2 (extRefl .w2) = extRefl w2
lower-pres-⟨⟩≽ I w2 w1 (extTrans h h₁) = extTrans (lower-pres-⟨⟩≽ I _ _ h) (lower-pres-⟨⟩≽ I _ _ h₁)
lower-pres-⟨⟩≽ I .(w1 ++ choice name t ∷ []) w1 (extChoice .w1 name l t res x x₁) =
  extChoice w1 name l t res x (lower-pres-allIW I (λ i → i w1 (res (length l) t)) x₁)
lower-pres-⟨⟩≽ I .(w1 ++ start name res ∷ []) w1 (extEntry .w1 name res x) = extEntry w1 name res x

data norepeats {A : Set} : List A → Set where
  norepsNil : norepeats []
  norepsCons : (a : A) (l : List A) → ¬ a ∈ l → norepeats l → norepeats (a ∷ l)

++[] : {A : Set} (l : List A) → l ++ [] ≡ l
++[] {A} [] = refl
++[] {A} (x ∷ l) rewrite ++[] l = refl


{--
-- Same as 'inWorld' but the entry might only contain an initial segment of what is in the world
data ∈worldExt : entry → world → Set where
  inweHd : (name : csName) (cs₁ cs₂ : List Term) (res : restriction) (w : world) → ∈worldExt (mkentry name cs₁ res) (mkentry name (cs₁ ++ cs₂) res ∷ w)
  inweTl : (e e' : entry) (w : world) (d : ¬ entry.name e ≡ entry.name e') → ∈worldExt e w → ∈worldExt e (e' ∷ w)

data ≽entry : entry → entry → Set where
  ee : (name : csName) (cs₁ cs₂ : List Term) (res : restriction)
       → ≽entry (mkentry name (cs₁ ++ cs₂) res) (mkentry name cs₁ res)

≽entry-sameName : (e2 e1 : entry) → ≽entry e2 e1 → entry.name e2 ≡ entry.name e1
≽entry-sameName .(mkentry name (cs₁ ++ cs₂) res) .(mkentry name cs₁ res) (ee name cs₁ cs₂ res) = refl

≽entry-trans : {e3 e2 e1 : entry} → ≽entry e3 e2 → ≽entry e2 e1 → ≽entry e3 e1
≽entry-trans {.(mkentry name ((cs₁ ++ cs₂) ++ cs₃) res)} {.(mkentry name (cs₁ ++ cs₂) res)} {.(mkentry name cs₁ res)} (ee name .(cs₁ ++ cs₂) cs₃ res) (ee .name cs₁ cs₂ .res) rewrite ++-assoc cs₁ cs₂ cs₃ =
  ee name cs₁ (cs₂ ++ cs₃) res

≽entry-refl : (e : entry) → ≽entry e e
≽entry-refl (mkentry name choices res) =
  subst (λ x → ≽entry (mkentry name x res) (mkentry name choices res))
        (++-[] choices)
        (ee _ _ _ _)

∈worldExt-≽entry : (e : entry) (w : world) → ∈worldExt e w → Σ entry (λ e' → ∈world e' w × ≽entry e' e)
∈worldExt-≽entry .(mkentry name cs₁ res) .(mkentry name (cs₁ ++ cs₂) res ∷ w) (inweHd name cs₁ cs₂ res w) =
  (mkentry name (cs₁ ++ cs₂) res , inwHd _ _ , ee _ _ _ _)
∈worldExt-≽entry e .(e' ∷ w) (inweTl .e e' w d i) =
  let (e'' , iw , ext) = ∈worldExt-≽entry e w i in
  let z = ≽entry-sameName _ _ ext in
  (e'' , inwTl _ _ _ (subst (λ x → ¬ x ≡ entry.name e') (sym z) d) iw , ext)

≽entry-∈worldExt : (e e' : entry) (w : world) → ∈world e' w → ≽entry e' e → ∈worldExt e w
≽entry-∈worldExt .(mkentry name cs₁ res) .(mkentry name (cs₁ ++ cs₂) res) .(mkentry name (cs₁ ++ cs₂) res ∷ w) (inwHd .(mkentry name (cs₁ ++ cs₂) res) w) (ee name cs₁ cs₂ res) =
  inweHd _ _ _ _ _
≽entry-∈worldExt e e' .(e'' ∷ w) (inwTl .e' e'' w d i) ext =
  inweTl e e'' w (subst (λ x → ¬ x ≡ entry.name e'') (≽entry-sameName _ _ ext) d) (≽entry-∈worldExt e e' w i ext)

∈world-∈worldExt : {e : entry} {w : world} → ∈world e w → ∈worldExt e w
∈world-∈worldExt {e} {w} i = ≽entry-∈worldExt _ _ _ i (≽entry-refl _)

∈world-∈wdom : {e : entry} {w : world} → ∈world e w → entry.name e ∈ wdom w
∈world-∈wdom {e} {.(e ∷ w)} (inwHd .e w) = here refl
∈world-∈wdom {e} {.(e' ∷ w)} (inwTl .e e' w d i) = there (∈world-∈wdom i)


record ≽world (I : InhW) (w2 : world) (w1 : world) : Set where
  constructor mkext
  field
    ext   : (e : entry) → ∈world e w1 → ∈worldExt e w2
    wf    : wfWorld (I w2) w1 → wfWorld (I w2) w2
    norep : norepeats (wdom w1) → norepeats (wdom w2)
--
-- in 'wf', if we use 'wfWorld (I w1) w1 → wfWorld (I w2) w2' then to prove ext:'⟨ I ⟩ (mkentry name [] res ∷ w) ⪰ w'
-- we have to prove that 'wfWorld (I w) w → wfWorld (I (mkentry name [] res ∷ w)) w', which is essentially the
-- monotonicity of 'I', which assumes ext, which we're trying to prove
--
-- if we use 'wfWorld (I w2) w1 → wfWorld (I w2) w2' then to prove the transitivity of [_]_⪰_ we have to "lower"
-- 'I w3' to 'I w1' to make use of the 1st hypothesis --> doesn't make sense
--
-- if we use 'wfWorld (I w1) w1 → wfWorld (I w1) w2' then it doesn't quite make sense that the larger world should
-- be true w.r.t. the smaller one
--

{--
 A world could be a flat list of choices instead
--}

⟨_⟩_⪰_ : (I : InhW) (w2 : world) (w1 : world) → Set
⟨ I ⟩ w2 ⪰ w1 = ≽world I w2 w1
--}

{--≽entry-pres-∈worldExt : {e e' : entry} {w : world} → ≽entry e' e → ∈worldExt e' w → ∈worldExt e w
≽entry-pres-∈worldExt {e} {e'} {w} ext i =
  let (e'' , i' , ext') = ∈worldExt-≽entry _ _ i in
  ≽entry-∈worldExt _ _ _ i' (≽entry-trans ext' ext)

inhW-mon : (I : InhW) → Set
inhW-mon I = (w2 w1 : world) (t : Term) → ⟨ I ⟩ w2 ⪰ w1 → I w1 t → I w2 t

inh-mon : (I : Inh) → Set
inh-mon (m , n , f) = (j : ℕ) (c₁ : m ≤ j) (c₂ : j ≤ n) → inhW-mon (f j c₁ c₂)

inhW-mon-wfChoices : (I : InhW) (mon : inhW-mon I) (w1 w2 : world) (l : List Term) (res : restriction)
                     → ⟨ I ⟩ w2 ⪰ w1
                     → wfChoices (I w1) l res
                     → wfChoices (I w2) l res
inhW-mon-wfChoices I mon w1 w2 [] res ext wf = tt
inhW-mon-wfChoices I mon w1 w2 (x ∷ l) res ext (wf1 , wf2) =
  (mon _ _ _ ext wf1 , inhW-mon-wfChoices I mon w1 w2 l (lift res) ext wf2)

inhW-mon-wfEntry : (I : InhW) (mon : inhW-mon I) (w1 w2 : world) (e : entry) → ⟨ I ⟩ w2 ⪰ w1 → wfEntry (I w1) e → wfEntry (I w2) e
inhW-mon-wfEntry I mon w1 w2 (mkentry name choices res) ext wf = inhW-mon-wfChoices I mon _ _ _ _ ext wf

inhW-mon-wfWorld : (I : InhW) (mon : inhW-mon I) (w1 w2 w : world) → ⟨ I ⟩ w2 ⪰ w1 → wfWorld (I w1) w → wfWorld (I w2) w
inhW-mon-wfWorld I mon w1 w2 [] ext wf = tt
inhW-mon-wfWorld I mon w1 w2 (x ∷ w) ext (wf1 , wf2) =
  (inhW-mon-wfEntry I mon _ _ x ext wf1 , inhW-mon-wfWorld I mon w1 w2 w ext wf2)

peTrans : {I : InhW} {w1 w2 w3 : world} (mon : inhW-mon I) (e1 : ⟨ I ⟩ w3 ⪰ w2) (e2 : ⟨ I ⟩ w2 ⪰ w1) → ⟨ I ⟩ w3 ⪰ w1
peTrans {I} {w1} {w2} {w3} mon (mkext ext2 wf2 norep2) (mkext ext1 wf1 norep1) =
  mkext
    (λ e i → let (e' , i' , ext') = ∈worldExt-≽entry _ _ (ext1 e i) in
              ≽entry-pres-∈worldExt ext' (ext2 e' i'))
    (λ wf → wf2 {!!})
    λ nr → norep2 (norep1 nr)
--}

[]≽-trans : {I : Inh} {w1 w2 w3 : world} (e1 : [ I ] w3 ⪰ w2) (e2 : [ I ] w2 ⪰ w1) → [ I ] w3 ⪰ w1
[]≽-trans {I} {w1} {w2} {w3} e1 e2 = extTrans e1 e2

{--peRefl : (I : InhW) (w : world) → ⟨ I ⟩ w ⪰ w
peRefl I w = mkext (λ e i → ∈world-∈worldExt i) (λ x → x) λ x → x
--}

[]≽-refl : (I : Inh) (w : world) → [ I ] w ⪰ w
[]≽-refl I w = extRefl _

{--peEntry : (I : InhW) (w : world) (name : csName) (res : restriction)
          → ¬ (name ∈ wdom w)
          → ⟨ I ⟩ (mkentry name [] res ∷ w) ⪰ w
peEntry I w name res ni =
  mkext (λ e i → inweTl _ _ _ (λ x → ni (subst (λ z → z ∈ wdom w) x (∈world-∈wdom i))) (∈world-∈worldExt i))
        (λ wf → (tt , {!!}))
        λ norep → norepsCons _ _ ni norep
--}

[]≽newcs : (I : Inh) (w : world) (name : csName) (res : restriction)
         → ¬ (name ∈ wdom w)
         → [ I ] (newcs w name res) ⪰ w
[]≽newcs I w name res ni = extEntry _ _ _ ni

wdom++ : (w₁ w₂ : world) → wdom (w₁ ++ w₂) ≡ wdom w₁ ++ wdom w₂
wdom++ [] w₂ = refl
wdom++ (start name res ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl
wdom++ (choice name t ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl

wdomAddChoice : (w : world) (name : csName) (t : Term) → wdom (w ∷ʳ choice name t) ≡ wdom w
wdomAddChoice w name t rewrite wdom++ w [ choice name t ] rewrite ++[] (wdom w) = refl

wdomAddStart : (w : world) (name : csName) (r : restriction) → wdom (w ∷ʳ start name r) ≡ wdom w ∷ʳ name
wdomAddStart w name r rewrite wdom++ w [ start name r ] = refl

∈[1] : {A : Set} {a b : A} → a ∈ [ b ] → a ≡ b
∈[1] {A} {a} {b} (here px) = px

∈∷-∈∷ʳ : {A : Set} {a b : A} {l : List A} → ¬ b ∈ l → b ∈ l ∷ʳ a → a ∈ b ∷ l
∈∷-∈∷ʳ {A} {a} {b} {l} ni i with ∈-++⁻ l i
... | inj₁ p = ⊥-elim (ni p)
... | inj₂ (here p) = here (sym p)

norepeats∷ʳ : {A : Set} (l : List A) (a : A) → norepeats l → ¬ a ∈ l → norepeats (l ∷ʳ a)
norepeats∷ʳ {A} [] a norep ni = norepsCons a [] ni norep
norepeats∷ʳ {A} (x ∷ l) a (norepsCons .x .l x₁ norep) ni =
  norepsCons
    x (l ∷ʳ a)
    (λ x → ⊥-elim (ni (∈∷-∈∷ʳ x₁ x)))
    (norepeats∷ʳ l a norep λ x → ni (there x))

extwPreservesNorepeats : (I : Inh) (w1 w2 : world) → ⟨ I ⟩ w2 ⪰ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extwPreservesNorepeats I w1 .w1 (extRefl .w1) norep = norep
extwPreservesNorepeats I w1 w2 (extTrans e e₁) norep = extwPreservesNorepeats _ _ _ e (extwPreservesNorepeats _ _ _ e₁ norep)
extwPreservesNorepeats I w1 .(w1 ++ choice name t ∷ []) (extChoice .w1 name l t res x x₁) norep rewrite wdomAddChoice w1 name t = norep
extwPreservesNorepeats I w1 .(w1 ++ start name res ∷ []) (extEntry .w1 name res x) norep rewrite wdomAddStart w1 name res =
  norepeats∷ʳ _ _ norep x

{--extPreservesNorepeats : (I : Inh) (w1 w2 : world) → [ I ] w2 ⪰ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extPreservesNorepeats I w1 w2 e norep = extwPreservesNorepeats (topInh I) w1 w2 e norep--}

{--worldw : Inh → Set
worldw I = Σ world (wfWorld I)

_⪰·_ : {I : Inh} (w2 : worldw I) (w1 : worldw I) → Set
w2 ⪰· w1 = proj₁ w2 ⪰ proj₁ w1--}

wPred : (I : Inh) (w : world) → Set₁
wPred I w = (w' : world) (e : [ I ] w' ⪰ w) → Set

wPredExtIrr : {I : Inh} {w : world} (f : wPred I w) → Set
wPredExtIrr {I} {w} f = (w' : world) (e1 e2 : [ I ] w' ⪰ w) → f w' e1 → f w' e2

-- f holds in all extensions
allW : (I : Inh) (w : world) (f : wPred I w) → Set
allW I w f = ∀ (w' : world) (e : [ I ] w' ⪰ w) → f w' e

-- f holds in one extensions
exW : (I : Inh) (w : world) (f : wPred I w) → Set
exW I w f = Σ world (λ w' → Σ ([ I ] w' ⪰ w) (λ e → f w' e))

exAllW : (I : Inh) (w : world) (f : wPred I w) → Set
exAllW I w f = exW I w (λ w1 e1 → allW I w1 (λ w2 e2 → f w2 ([]≽-trans {I}e2 e1)))

-- f holds in an open bar
inOpenBar : (I : Inh) (w : world) (f : wPred I w) → Set
inOpenBar I w f =
  allW I w (λ w1 e1 → exW I w1 (λ w2 e2 → allW I w2 (λ w3 e3 →
     f w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2 e1)))))

-- f holds in an open bar that depends on another open bar h
inOpenBar' : (I : Inh) (w : world) {g : wPred I w} (h : inOpenBar I w g) (f : ∀ w' (e : [ I ] w' ⪰ w) (x : g w' e) → Set) → Set
inOpenBar' I w h f =
  allW I w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW I w1 (λ w2 e2 → allW I w2 (λ w3 e3 →
             let e' = []≽-trans {I} e3 e2 in
             f w3 ([]≽-trans {I} e' ([]≽-trans {I} e1 e0)) (q w3 e'))))
\end{code}


We now define part of OpenTT's syntax and postulate its operational semantics.


\begin{code}
-- similar to lookup
select : {A : Set} (n : ℕ) (l : List A) → Maybe A
select {A} n [] = nothing
select {A} 0 (x ∷ l) = just x
select {A} (suc n) (x ∷ l) = select n l

getChoice : (n : ℕ) (name : csName) (w : world) → Maybe Term
getChoice n name w with getCs name w
... | just (mkcs _ l _) = select n l
... | nothing = nothing

step : ∀ (T : Term) (w : world) → Maybe Term
-- VAR
step (VAR v) w = nothing
-- NAT
step NAT w = just NAT
-- QNAT
step QNAT w = just QNAT
-- LT
step (LT a b) w = just (LT a b)
-- QLT
step (QLT a b) w = just (QLT a b)
-- NUM
step (NUM n) w = just (NUM n)
-- PI
step (PI a b) w = just (PI a b)
-- LAMBDA
step (LAMBDA t) w = just (LAMBDA t)
-- APPLY
step (APPLY (CS name) (NUM n)) w = getChoice n name w
step (APPLY (CS name) t) w with step t w
... | just u = just (APPLY (CS name) u)
... | nothing = nothing
step (APPLY (LAMBDA t) u) w = just (sub u t)
step (APPLY f a) w with step f w
... | just g = just (APPLY g a)
... | nothing = nothing
-- SUM
step (SUM a b) w = just (SUM a b)
-- PAIR
step (PAIR a b) w = just (PAIR a b)
-- SPREAD
step (SPREAD a b) w = nothing -- TODO
-- SET
step (SET a b) w = just (SET a b)
-- UNION
step (UNION a b) w = just (UNION a b)
-- INL
step (INL a) w = just (INL a)
-- INR
step (INR a) w = just (INR a)
-- DECIDE
step (DECIDE a b c) w = nothing -- TODO
-- EQ
step (EQ a b c) w = just (EQ a b c)
-- AX
step AX w = just AX
-- FREE
step FREE w = just FREE
-- CS
step (CS name) w = just (CS name)
-- TSQUASH
step (TSQUASH a) w = just (TSQUASH a)
-- FFDEFS
step (FFDEFS a b) w = just (FFDEFS a b)
-- UNIV
step (UNIV u) w = just (UNIV u)
-- LOWER
step (LOWER t) w = just (LOWER t)
-- LOWER
step (SHRINK t) w = just (SHRINK t)

steps : (n : ℕ) (t : Term) (w : world) → Term
steps 0 t w = t
steps (suc n) t w with step t w
... | just u = steps n u w
... | nothing = t

_⇓_at_ : ∀ (T T' : Term) (w : world) → Set
T ⇓ T' at w = Σ ℕ (λ n → steps n T w ≡ T')
infix 30 _⇓_at_

⇓-refl : (T : Term) (w : world) → T ⇓ T at w
⇓-refl T w = (0 , refl)

-- values compute to themselves
stepVal : (a : Term) (w : world) → isValue a → step a w ≡ just a
stepVal NAT w v = refl
stepVal QNAT w v = refl
stepVal (NUM x) w v = refl
stepVal (PI a a₁) w v = refl
stepVal (LAMBDA a) w v = refl
stepVal (SUM a a₁) w v = refl
stepVal (PAIR a a₁) w v = refl
stepVal (SET a a₁) w v = refl
stepVal (UNION a a₁) w v = refl
stepVal (INL a) w v = refl
stepVal (INR a) w v = refl
stepVal (EQ a a₁ a₂) w v = refl
stepVal AX w v = refl
stepVal FREE w v = refl
stepVal (CS x) w v = refl
stepVal (TSQUASH a) w v = refl
stepVal (FFDEFS a a₁) w v = refl
stepVal (UNIV x) w v = refl
stepVal (LOWER a) w v = refl
stepVal (SHRINK a) w v = refl

stepsVal : (a : Term) (w : world) (n : ℕ) → isValue a → steps n a w ≡ a
stepsVal a w 0 v = refl
stepsVal a w (suc n) v rewrite stepVal a w v = stepsVal a w n v

compVal : (a b : Term) (w : world) → a ⇓ b at w → isValue a → a ≡ b
compVal a b w (n , c) v rewrite stepsVal a w n v = c

postulate
  -- Howe's computational equivalence relation
  _∼_at_ : ∀ (T T' : Term) (w : world) → Set
  -- states that the argument does not contain any definition or choice sequence
  nodefs : Term → Set
infix 30 _∼_at_


-- T computes to T' in all extensions of w
[_]_⇛_at_ : (I : Inh) (T T' : Term) (w : world) → Set
[ I ] T ⇛ T' at w = allW I w (λ w' _ → T ⇓ T' at w')
infix 30 [_]_⇛_at_

-- T computationally equivalent to T' in all extensions of w
[_]_≈_at_ : (I : Inh) (T T' : Term) (w : world) → Set
[ I ] T ≈ T' at w = allW I w (λ w' _ → T ∼ T' at w')
infix 30 [_]_≈_at_

compAllRefl : (I : Inh) (T : Term) (w : world) → [ I ] T ⇛ T at w
compAllRefl I T w =  λ w' e → ⇓-refl T w'

compAllVal : (I : Inh) {a b : Term} {w : world} → [ I ] a ⇛ b at w → isValue a → a ≡ b
compAllVal I {a} {b} {w} c i = let c' = c _ ([]≽-refl I w) in compVal _ _ _ c' i

-- t1 and t2 compute to the same number and stay the same number in all extensions
strongMonEq : (I : Inh) (w : world) (t1 t2 : Term) → Set
strongMonEq I w t1 t2 = Σ ℕ (λ n → [ I ] t1 ⇛ (NUM n) at w × [ I ] t2 ⇛ (NUM n) at w)

-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : (I : Inh) (w : world) (t1 t2 : Term) → Set
weakMonEq I w t1 t2 = allW I w (λ w' _ → Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w'))


[]⇛-mon : (I : Inh) {a b : Term} {w2 w1 : world}
           → [ I ] w2 ⪰ w1
           → [ I ] a ⇛ b at w1
           → [ I ] a ⇛ b at w2
[]⇛-mon I {a} {b} {w2} {w1} ext c w' e' = c w' ([]≽-trans {I} e' ext)

getChoices++ : (name : csName) (w w' : world)
               → getChoices name (w ++ w') ≡ getChoices name w ++ getChoices name w'
getChoices++ name [] w' = refl
getChoices++ name (start name₁ res ∷ w) w' = getChoices++ name w w'
getChoices++ name (choice name₁ t ∷ w) w' with name ≟ name₁
... | yes p rewrite getChoices++ name w w' = refl
... | no p = getChoices++ name w w'

just-inj : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl =  refl

mkcs-inj1 : {n1 n2 : csName} {l1 l2 : List Term} {r1 r2 : restriction} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → n1 ≡ n2
mkcs-inj1 refl =  refl

mkcs-inj2 : {n1 n2 : csName} {l1 l2 : List Term} {r1 r2 : restriction} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → l1 ≡ l2
mkcs-inj2 refl =  refl

mkcs-inj3 : {n1 n2 : csName} {l1 l2 : List Term} {r1 r2 : restriction} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → r1 ≡ r2
mkcs-inj3 refl =  refl

getCs++ : (name : csName) (w w' : world) (l : List Term) (r : restriction)
          → getCs name w ≡ just (mkcs name l r)
          → getCs name (w ++ w') ≡ just (mkcs name (l ++ getChoices name w') r)
getCs++ name (start name₁ res ∷ w) w' l r e with name ≟ name₁
... | yes p rewrite getChoices++ name w w' rewrite mkcs-inj2 (just-inj e) rewrite mkcs-inj3 (just-inj e) = refl
... | no p = getCs++ name w w' l r e
getCs++ name (choice name₁ t ∷ w) w' l r e = getCs++ name w w' l r e

getCs++-same-choice : (name : csName) (w : world) (l : List Term) (r : restriction) (t : Term)
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name t ]) ≡ just (mkcs name (l ++ [ t ]) r)
getCs++-same-choice name w l r t e rewrite getCs++ name w [ choice name t ] l r e with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)

getCs++-diff-choice : (name name₁ : csName) (w : world) (l : List Term) (r : restriction) (t : Term)
                      → ¬ name ≡ name₁
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name₁ t ]) ≡ just (mkcs name l r)
getCs++-diff-choice name name₁ w l r t d e rewrite getCs++ name w [ choice name₁ t ] l r e with name ≟ name₁
... | yes p = ⊥-elim (d p)
... | no p rewrite ++[] l = refl

⟨⟩≽-pres-∈world : {I : Inh} {w1 w2 : world} {name : csName} {l : List Term} {r : restriction}
                  → ⟨ I ⟩ w2 ⪰ w1
                  → ∈world (mkcs name l r) w1
                  → Σ (List Term) (λ l' → ∈world (mkcs name (l ++ l') r) w2)
⟨⟩≽-pres-∈world {I} {w1} {.w1} {name} {l} {r} (extRefl .w1) i =
  ([] , subst (λ x → ∈world (mkcs name x r) w1) (sym (++[] l)) i)
⟨⟩≽-pres-∈world {I} {w1} {w2} {name} {l} {r} (extTrans e e₁) i =
  let (l1 , i1) = ⟨⟩≽-pres-∈world e₁ i in
  let (l2 , i2) = ⟨⟩≽-pres-∈world e i1 in
  (l1 ++ l2 , subst (λ x → ∈world (mkcs name x r) w2) (++-assoc l l1 l2) i2)
⟨⟩≽-pres-∈world {I} {w1} {.(w1 ++ choice name₁ t ∷ [])} {name} {l} {r} (extChoice .w1 name₁ l₁ t res x x₁) i with name ≟ name₁
... | yes p rewrite p = ([ t ] , getCs++-same-choice name₁ w1 l r t i)
... | no p rewrite getCs++-diff-choice name name₁ w1 l r t p i =
  ([] , subst (λ x → just (mkcs name l r) ≡ just (mkcs name x r)) (sym (++[] l)) refl)
⟨⟩≽-pres-∈world {I} {w1} {.(w1 ++ start name₁ res ∷ [])} {name} {l} {r} (extEntry .w1 name₁ res x) i rewrite getCs++ name w1 [ start name₁ res ] l r i =
  ([] , refl)

[]≽-pres-∈world : {I : Inh} {w1 w2 : world} {name : csName} {l : List Term} {r : restriction}
                  → [ I ] w2 ⪰ w1
                  → ∈world (mkcs name l r) w1
                  → Σ (List Term) (λ l' → ∈world (mkcs name (l ++ l') r) w2)
[]≽-pres-∈world {I} {w1} {w2} {name} {l} {r} e i = ⟨⟩≽-pres-∈world e i

suc≤len∷ʳ : {A : Set} (l : List A) (a : A) (k : ℕ) → k ≤ length l → suc k ≤ length (l ∷ʳ a)
suc≤len∷ʳ {A} l a k h rewrite length-++ l {[ a ]} rewrite +-comm (length l) 1 = _≤_.s≤s h

suc≤len++∷ʳ : {A : Set} (k : ℕ) (l1 l2 : List A) (a : A)
              → k ≤ length l1
              → suc k ≤ length ((l1 ++ l2) ∷ʳ a)
suc≤len++∷ʳ {A} k l1 l2 a h = suc≤len∷ʳ (l1 ++ l2) a k (subst (λ x → k ≤ x) (sym (length-++ l1 {l2})) (≤-stepsʳ (length l2) h))

∈world-extcs : (w : world) (name : csName) (l : List Term) (r : restriction) (t : Term)
               → ∈world (mkcs name l r) w
               → ∈world (mkcs name (l ∷ʳ t) r) (extcs w name t)
∈world-extcs w name l r t i rewrite getCs++ name w [ choice name t ] l r i with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)

getCs++∉ : (name : csName) (w w' : world)
          → getCs name w ≡ nothing
          → getCs name (w ++ w') ≡ getCs name w'
getCs++∉ name [] w' h = refl
getCs++∉ name (start name₁ res ∷ w) w' h with name ≟ name₁
getCs++∉ name (start name₁ res ∷ w) w' () | yes p
... | no p = getCs++∉ name w w' h
getCs++∉ name (choice name₁ t ∷ w) w' h = getCs++∉ name w w' h

∉-getCs-nothing : (w : world) (name : csName) → ¬ (name ∈ (wdom w)) → getCs name w ≡ nothing
∉-getCs-nothing [] name i = refl
∉-getCs-nothing (start name₁ res ∷ w) name i with name ≟ name₁
... | yes p rewrite p = ⊥-elim (i (here refl))
... | no p = ∉-getCs-nothing w name λ j → i (there j)
∉-getCs-nothing (choice name₁ t ∷ w) name i = ∉-getCs-nothing w name i

∈world-newcs : (w : world) (name : csName) (r : restriction)
               → ¬ (name ∈ (wdom w))
               → ∈world (mkcs name [] r) (newcs w name r)
∈world-newcs w name r ni rewrite getCs++∉ name w [ start name r ] (∉-getCs-nothing w name ni) with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)

suc-≢-0 : {n : ℕ} → ¬ suc n ≡ 0
suc-≢-0 {n} ()

select-last : {A : Set} (l : List A) (a : A)
              → select (length l) (l ++ [ a ]) ≡ just a
select-last {A} [] a = refl
select-last {A} (x ∷ l) a = select-last l a

getChoice-extcs-last : (w : world) (k : ℕ) (name : csName) (l : List Term) (r : restriction) (t : Term)
                       → k ≡ length l
                       → getCs name w ≡ just (mkcs name l r)
                       → getChoice k name (extcs w name t) ≡ just t
getChoice-extcs-last w k name l r t e h rewrite e | getCs++ name w [ choice name t ] l r h with name ≟ name
... | yes p = select-last l t
... | no p = ⊥-elim (p refl)

≤-s≤s-≡ : (i k : ℕ) → i ≤ k → suc k ≤ suc i → k ≡ i
≤-s≤s-≡ i k a (_≤_.s≤s b) = ≤∧≮⇒≡ b (≤⇒≯ a)

⟨⟩≽-ΣgetChoice : (I : Inh) (w1 w2 : world) (name : csName) (l1 l2 : List Term) (r : restriction) (k : ℕ)
                 → ∈world (mkcs name l1 r) w1
                 → ∈world (mkcs name l2 r) w2
                 → length l1 ≤ k
                 → k < length l2
                 → ⟨ I ⟩ w2 ⪰ w1
                 → Σ Term (λ t → Σ world (λ w → Σ (List Term) (λ l →
                       getChoice k name (extcs w name t) ≡ just t
                     × ∈world (mkcs name l r) w
                     × k ≡ length l
                     × ⟨ I ⟩ w2 ⪰ (extcs w name t)
                     × ⟨ I ⟩ w ⪰ w1
                     × allIW I (λ i → i w (r k t)))))
⟨⟩≽-ΣgetChoice I w1 .w1 name l1 l2 r k i1 i2 len1 len2 (extRefl .w1)
  rewrite i1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
⟨⟩≽-ΣgetChoice I w1 w2 name l1 l2 r k i1 i2 len1 len2 (extTrans {w1} {w3} {w2} ext ext₁) with ⟨⟩≽-pres-∈world ext₁ i1
... | (l , iw) with k <? length (l1 ++ l)
...            | yes p =
  let (t , w , l0 , h1 , h2 , h3 , h4 , h5 , h6) = ⟨⟩≽-ΣgetChoice I w1 w3 name l1 (l1 ++ l) r k i1 iw len1 p ext₁ in
  (t , w , l0 , h1 , h2 , h3 , extTrans {I} ext h4 , h5 , h6)
...            | no p =
  let (t , w , l0 , h1 , h2 , h3 , h4 , h5 , h6) = ⟨⟩≽-ΣgetChoice I w3 w2 name (l1 ++ l) l2 r k iw i2 (≮⇒≥ p) len2 ext in
  (t , w , l0 , h1 , h2 , h3 , h4 , extTrans {I} h5 ext₁ , h6)
⟨⟩≽-ΣgetChoice I w1 .(w1 ++ choice name₁ t ∷ []) name l1 l2 r k i1 i2 len1 len2 (extChoice .w1 name₁ l t res x x₁) with name ≟ name₁
... | yes p rewrite p | x | sym (mkcs-inj2 (just-inj i1))
                    | sym (mkcs-inj3 (just-inj i1))
                    | getCs++ name₁ w1 [ choice name₁ t ] l res x
                    | sym (mkcs-inj2 (just-inj i2))
            with name₁ ≟ name₁
...         | yes q rewrite length-++ l {[ t ]} | +-comm (length l) 1 =
              let len : k ≡ length l
                  len = ≤-s≤s-≡ _ _ len1 len2 in
                  (t , w1 , l , getChoice-extcs-last w1 k name₁ l res t len x ,
                    x , len , extRefl (extcs w1 name₁ t) , extRefl w1 , subst (λ x → allIW I (λ i → i w1 (res x t))) (sym len) x₁)
...         | no q rewrite ++[] l = ⊥-elim (1+n≰n (≤-trans len2 len1))
⟨⟩≽-ΣgetChoice I w1 .(w1 ++ choice name₁ t ∷ []) name l1 l2 r k i1 i2 len1 len2 (extChoice .w1 name₁ l t res x x₁)
    | no p rewrite getCs++ name w1 [ choice name₁ t ] l1 r i1
           with name ≟ name₁
...        | yes q = ⊥-elim (p q)
...        | no q rewrite ++[] l1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
⟨⟩≽-ΣgetChoice I w1 .(w1 ++ start name₁ res ∷ []) name l1 l2 r k i1 i2 len1 len2 (extEntry .w1 name₁ res x) with name ≟ name₁
... | yes p rewrite p | getCs++ name₁ w1 [ start name₁ res ] l1 r i1 | ++[] l1 | sym (mkcs-inj2 (just-inj i2)) =
  ⊥-elim (1+n≰n (≤-trans len2 len1))
... | no p rewrite getCs++ name w1 [ start name₁ res ] l1 r i1 | ++[] l1 | sym (mkcs-inj2 (just-inj i2)) =
  ⊥-elim (1+n≰n (≤-trans len2 len1))


[]≽-ΣgetChoice : (I : Inh) (w1 w2 : world) (name : csName) (l : List Term) (r : restriction) (k : ℕ)
                 → ¬ name ∈ wdom w1
                 → [ I ] w2 ⪰ newcs w1 name r
                 → k < length l
                 → ∈world (mkcs name l r) w2
                 → Σ Term (λ t → Σ world (λ w → Σ (List Term) (λ l →
                       getChoice k name (extcs w name t) ≡ just t
                     × ∈world (mkcs name l r) w
                     × k ≡ length l
                     × [ I ] w2 ⪰ extcs w name t
                     × [ I ] w ⪰ newcs w1 name r
                     × allIW I (λ i → i w (r k t)))))
[]≽-ΣgetChoice I w1 w2 name l r k niw ext len i =
  let j = ∈world-newcs w1 name r niw in
  ⟨⟩≽-ΣgetChoice I (newcs w1 name r) w2 name [] l r k j i _≤_.z≤n len ext

\end{code}
