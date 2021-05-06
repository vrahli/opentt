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
open import calculus
\end{code}



We first postulate and define enough about worlds to interpret OpenTT
w.r.t. open bars.


\begin{code}
restriction : Set
restriction = (n : ℕ) → Term → Term

lift : restriction → restriction
lift res n t = res (suc n) t

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

{--wfChoices : InhT → List Term → restriction → Set
wfChoices I [] res = ⊤
wfChoices I (t ∷ ts) res = I (res 0 t) × wfChoices I ts (lift res)

wfEntry : InhT → entry → Set
wfEntry I (mkentry name choices res) = wfChoices I choices res

wfWorld : Inh → world → Set
wfWorld I [] = ⊤
wfWorld I (entry ∷ entries) = wfEntry (I entries) entry × wfWorld I entries--}

-- w2 extends w1
data ⟨_⟩_⪰_ (I : InhW) : (w2 : world) (w1 : world) → Set where
  extRefl : (w : world) → ⟨ I ⟩ w ⪰ w
  extTrans : {w1 w2 w3 : world} → ⟨ I ⟩ w3 ⪰ w2 → ⟨ I ⟩ w2 ⪰ w1 → ⟨ I ⟩ w3 ⪰ w1
  extChoices :
    (w : world) (name : choiceSeqName) (l : List Term) (t : Term) (res : restriction)
    → I w (res (length l) t)
    → ⟨ I ⟩ (mkentry name (l ∷ʳ t) res ∷ w) ⪰ (mkentry name l res ∷ w)
  extEntry :
    (w : world) (name : choiceSeqName) (res : restriction)
    → ¬ (name ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → ⟨ I ⟩ (mkentry name [] res ∷ w) ⪰ w

-- w2 extends w1
[_]_⪰_ : (I : Inh) (w2 : world) (w1 : world) → Set
[ (m , n , f) ] w2 ⪰ w1 = (j : ℕ) (c₁ : m ≤ j) (c₂ : j ≤ n) → ⟨ f j c₁ c₂ ⟩ w2 ⪰ w1

eTrans : {I : Inh} {w1 w2 w3 : world} (e1 : [ I ] w3 ⪰ w2) (e2 : [ I ] w2 ⪰ w1) → [ I ] w3 ⪰ w1
eTrans {I} {w1} {w2} {w3} e1 e2 j c₁ c₂ = extTrans (e1 j c₁ c₂) (e2 j c₁ c₂)

eRefl : (I : Inh) (w : world) → [ I ] w ⪰ w
eRefl I w j c₁ c₂ = extRefl w

eEntry : (I : Inh) (w : world) (name : choiceSeqName) (res : restriction)
         → ¬ (name ∈ wdom w)
         → [ I ] (mkentry name [] res ∷ w) ⪰ w
eEntry I w name res ni j c₁ c₂ = extEntry w name res ni


data norepeats {A : Set} : List A → Set where
  norepsNil : norepeats []
  norepsCons : (a : A) (l : List A) → ¬ a ∈ l → norepeats l → norepeats (a ∷ l)


extwPreservesNorepeats : (I : InhW) (w1 w2 : world) → ⟨ I ⟩ w2 ⪰ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extwPreservesNorepeats I w1 .w1 (extRefl .w1) norep = norep
extwPreservesNorepeats I w1 w2 (extTrans e e₁) norep = extwPreservesNorepeats _ _ _ e (extwPreservesNorepeats _ _ _ e₁ norep)
extwPreservesNorepeats I .(mkentry name l res ∷ w) .(mkentry name (l ++ t ∷ []) res ∷ w) (extChoices w name l t res x) norep = norep
extwPreservesNorepeats I w1 .(mkentry name [] res ∷ w1) (extEntry .w1 name res x) norep = norepsCons name (wdom w1) x norep

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
