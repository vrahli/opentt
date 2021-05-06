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
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_)
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

record entry : Set where
  constructor mkentry
  field
    name    : choiceSeqName
    choices : List Term
    res     : restriction

--  Worlds
world : Set
world = List entry

wdom : world → List choiceSeqName
wdom [] = []
wdom (mkentry name _ _ ∷ w) = name ∷ wdom w

InhT : Set₁
InhT = (t : Term) → Set

InhW : Set₁
InhW = (w : world) → InhT

InhF : ℕ → ℕ → Set₁
InhF m n = (j : ℕ) → m ≤ j → j ≤ n → InhW

Inh : Set₁
Inh = Σ ℕ λ m → Σ ℕ (λ n → InhF m n)

lower : Inh → Inh
lower (m , 0 , f) = (m , 0 , f)
lower (m , suc n , f) = (m , n , λ j c₁ c₂ → f j c₁ (≤-trans c₂ (n≤1+n _)))

lift : restriction → restriction
lift res n t = res (suc n) t

wfChoices : InhT → List Term → restriction → Set
wfChoices I [] res = ⊤
wfChoices I (t ∷ ts) res = I (res 0 t) × wfChoices I ts (lift res)

wfEntry : InhT → entry → Set
wfEntry I (mkentry name choices res) = wfChoices I choices res

wfWorld : InhT → world → Set
wfWorld I [] = ⊤
wfWorld I (entry ∷ entries) = wfEntry I entry × wfWorld I entries


-- w2 extends w1
data ⟨⟨_⟩⟩_⪰_ (I : InhW) : (w2 : world) (w1 : world) → Set where
  extRefl : (w : world) → ⟨⟨ I ⟩⟩ w ⪰ w
  extTrans : {w1 w2 w3 : world} → ⟨⟨ I ⟩⟩ w3 ⪰ w2 → ⟨⟨ I ⟩⟩ w2 ⪰ w1 → ⟨⟨ I ⟩⟩ w3 ⪰ w1
  extChoices :
    (w : world) (name : choiceSeqName) (l : List Term) (t : Term) (res : restriction)
    → I w (res (length l) t)
    → ⟨⟨ I ⟩⟩ (mkentry name (l ∷ʳ t) res ∷ w) ⪰ (mkentry name l res ∷ w)
  extEntry :
    (w : world) (name : choiceSeqName) (res : restriction)
    → ¬ (name ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → ⟨⟨ I ⟩⟩ (mkentry name [] res ∷ w) ⪰ w
--
-- The problem with this definition is that adding a new choice requires proving that it is inhabited
-- w.r.t. the previous state while by then we only know that it is inhabited w.r.t. a later state
--


data ∈world : entry → world → Set where
  inwHd : (e : entry) (w : world) → ∈world e (e ∷ w)
  inwTl : (e e' : entry) (w : world) (d : ¬ entry.name e ≡ entry.name e') → ∈world e w → ∈world e (e' ∷ w)

-- Same as 'inWorld' but the entry might only contain an initial segment of what is in the world
data ∈worldExt : entry → world → Set where
  inweHd : (name : choiceSeqName) (cs₁ cs₂ : List Term) (res : restriction) (w : world) → ∈worldExt (mkentry name cs₁ res) (mkentry name (cs₁ ++ cs₂) res ∷ w)
  inweTl : (e e' : entry) (w : world) (d : ¬ entry.name e ≡ entry.name e') → ∈worldExt e w → ∈worldExt e (e' ∷ w)

data ≽entry : entry → entry → Set where
  ee : (name : choiceSeqName) (cs₁ cs₂ : List Term) (res : restriction)
       → ≽entry (mkentry name (cs₁ ++ cs₂) res) (mkentry name cs₁ res)

≽entry-sameName : (e2 e1 : entry) → ≽entry e2 e1 → entry.name e2 ≡ entry.name e1
≽entry-sameName .(mkentry name (cs₁ ++ cs₂) res) .(mkentry name cs₁ res) (ee name cs₁ cs₂ res) = refl

≽entry-trans : {e3 e2 e1 : entry} → ≽entry e3 e2 → ≽entry e2 e1 → ≽entry e3 e1
≽entry-trans {.(mkentry name ((cs₁ ++ cs₂) ++ cs₃) res)} {.(mkentry name (cs₁ ++ cs₂) res)} {.(mkentry name cs₁ res)} (ee name .(cs₁ ++ cs₂) cs₃ res) (ee .name cs₁ cs₂ .res) rewrite ++-assoc cs₁ cs₂ cs₃ =
  ee name cs₁ (cs₂ ++ cs₃) res

++-[] : {A : Set} (l : List A) → l ++ [] ≡ l
++-[] {A} [] = refl
++-[] {A} (x ∷ l) rewrite ++-[] l = refl

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

data norepeats {A : Set} : List A → Set where
  norepsNil : norepeats []
  norepsCons : (a : A) (l : List A) → ¬ a ∈ l → norepeats l → norepeats (a ∷ l)


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


-- w2 extends w1
[_]_⪰_ : (I : Inh) (w2 : world) (w1 : world) → Set
[ (m , n , f) ] w2 ⪰ w1 = (j : ℕ) (c₁ : m ≤ j) (c₂ : j ≤ n) → ⟨ f j c₁ c₂ ⟩ w2 ⪰ w1

≽entry-pres-∈worldExt : {e e' : entry} {w : world} → ≽entry e' e → ∈worldExt e' w → ∈worldExt e w
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

eTrans : {I : Inh} {w1 w2 w3 : world} (e1 : [ I ] w3 ⪰ w2) (e2 : [ I ] w2 ⪰ w1) → [ I ] w3 ⪰ w1
eTrans {I} {w1} {w2} {w3} e1 e2 j c₁ c₂ = peTrans {!!} (e1 j c₁ c₂) (e2 j c₁ c₂)

peRefl : (I : InhW) (w : world) → ⟨ I ⟩ w ⪰ w
peRefl I w = mkext (λ e i → ∈world-∈worldExt i) (λ x → x) λ x → x

eRefl : (I : Inh) (w : world) → [ I ] w ⪰ w
eRefl I w j c₁ c₂ = peRefl _ _

peEntry : (I : InhW) (w : world) (name : choiceSeqName) (res : restriction)
          → ¬ (name ∈ wdom w)
          → ⟨ I ⟩ (mkentry name [] res ∷ w) ⪰ w
peEntry I w name res ni =
  mkext (λ e i → inweTl _ _ _ (λ x → ni (subst (λ z → z ∈ wdom w) x (∈world-∈wdom i))) (∈world-∈worldExt i))
        (λ wf → (tt , {!!}))
        λ norep → norepsCons _ _ ni norep

eEntry : (I : Inh) (w : world) (name : choiceSeqName) (res : restriction)
         → ¬ (name ∈ wdom w)
         → [ I ] (mkentry name [] res ∷ w) ⪰ w
eEntry I w name res ni j c₁ c₂ = peEntry _ _ _ _ ni



extwPreservesNorepeats : (I : InhW) (w1 w2 : world) → ⟨ I ⟩ w2 ⪰ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extwPreservesNorepeats I w1 w2 e norep = ≽world.norep e norep
-- extwPreservesNorepeats I w1 .w1 (extRefl .w1) norep = norep
-- extwPreservesNorepeats I w1 w2 (extTrans e e₁) norep = extwPreservesNorepeats _ _ _ e (extwPreservesNorepeats _ _ _ e₁ norep)
-- extwPreservesNorepeats I .(mkentry name l res ∷ w) .(mkentry name (l ++ t ∷ []) res ∷ w) (extChoices w name l t res x) norep = norep
-- extwPreservesNorepeats I w1 .(mkentry name [] res ∷ w1) (extEntry .w1 name res x) norep = norepsCons name (wdom w1) x norep

wfInh : (I : Inh) → Set
wfInh (m , n , f) = m ≤ n

extPreservesNorepeats : (I : Inh) (wf : wfInh I) (w1 w2 : world) → [ I ] w2 ⪰ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extPreservesNorepeats (m , n , f) wf w1 w2 e norep = extwPreservesNorepeats (f n wf ≤-refl) w1 w2 (e n wf ≤-refl) norep

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

-- f holds in an open bar
inOpenBar : (I : Inh) (w : world) (f : wPred I w) → Set
inOpenBar I w f =
  allW I w (λ w1 e1 → exW I w1 (λ w2 e2 → allW I w2 (λ w3 e3 →
     f w3 (eTrans {I} e3 (eTrans {I} e2 e1)))))

-- f holds in an open bar that depends on another open bar h
inOpenBar' : (I : Inh) (w : world) {g : wPred I w} (h : inOpenBar I w g) (f : ∀ w' (e : [ I ] w' ⪰ w) (x : g w' e) → Set) → Set
inOpenBar' I w h f =
  allW I w (λ w0 e0 →
           let p  = h w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW I w1 (λ w2 e2 → allW I w2 (λ w3 e3 →
             let e' = eTrans {I} e3 e2 in
             f w3 (eTrans {I} e' (eTrans {I} e1 e0)) (q w3 e'))))
\end{code}


We now define part of OpenTT's syntax and postulate its operational semantics.


\begin{code}
postulate
  -- operational semantics of the language
  _⇓_at_ : ∀ (T T' : Term) (w : world) → Set
  -- 'computes to' is reflexive
  compRefl : ∀ (T : Term) (w : world) → T ⇓ T at w
  -- values compute to themselves
  compVal : ∀ (a b : Term) (w : world) → a ⇓ b at w → isValue a → a ≡ b
  -- Howe's computational equivalence relation
  _∼_at_ : ∀ (T T' : Term) (w : world) → Set
  -- states that the argument does not contain any definition or choice sequence
  nodefs : Term → Set
infix 30 _⇓_at_
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
compAllRefl I T w =  λ w' e → compRefl T w'

compAllVal : (I : Inh) {a b : Term} {w : world} → [ I ] a ⇛ b at w → isValue a → a ≡ b
compAllVal I {a} {b} {w} c i = let c' = c _ (eRefl I w) in compVal _ _ _ c' i

-- t1 and t2 compute to the same number and stay the same number in all extensions
strongMonEq : (I : Inh) (w : world) (t1 t2 : Term) → Set
strongMonEq I w t1 t2 = Σ ℕ (λ n → [ I ] t1 ⇛ (NUM n) at w × [ I ] t2 ⇛ (NUM n) at w)

-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : (I : Inh) (w : world) (t1 t2 : Term) → Set
weakMonEq I w t1 t2 = allW I w (λ w' _ → Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w'))
\end{code}
