\begin{code}
{-# OPTIONS --rewriting #-}

open import bar

module theory (b : bar.Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import calculus
open import world
\end{code}



We now provide an inductive-recursive realizability semantics of
OpenTT.


\begin{code}
inbar : (w : world) (f : wPred w) → Set₁
--inbar = Bar.inBar b
inbar = inOpenBar

inbar' : (w : world) {g : wPred w} (h : inbar w g) (f : wPredDep g) → Set₁
--inbar' = Bar.inBar' b
inbar' = inOpenBar'

atbar : {w : world} {f : wPred w} (i : inbar w f) (w' : world) (e' : w' ≽ w) (p : f w' e') → Set₁
--atbar = Bar.atBar b
atbar = atOpenBar

↑inbar : {w : world} {f : wPred w} (i : inbar w f) {w' : world} (e : w' ≽ w) → inbar w' (↑wPred f e)
↑inbar = ↑inOpenBar

↑'inbar : {w : world} {f : wPred w} (i : inbar w f) {w' : world} (e : w' ≽ w) → inbar w' (↑wPred' f e)
--↑'inbar = Bar.↑'inBar b
↑'inbar = ↑'inOpenBar

↑inbar' : {w : world} {f : wPred w} {g : wPredDep f} (i : inbar w f) {w' : world} (e : w' ≽ w)
          → inbar' w i g → inbar' w' (↑inbar i e) (↑wPredDep g e)
↑inbar' {w} {f} {g} = ↑inOpenBar' {w} {f} {g}

wpreddepextirr : {w : world} {f : wPred w} (h : wPredDep f) (i : inbar w f) → Set₁
wpreddepextirr = wPredDepExtIrr-inOpenBar


-- PERs and world dependent PERs
per : Set₂
per = Term → Term → Set₁

wper : Set₂
wper = (w : world) → per

-- eqTypes and eqInType provide meaning to types w.r.t. already interpreted universes,
-- given by univs (1st conjunct defines the equality between such universes, while the
-- second conjunct defines the equality in such universes)
univs : Set₂
univs = Σ ℕ (λ n → wper × wper)

-- equality between types (an inductive definition)
-- and equality in types (a recursive function)
-- We don't check positivity here, this can be done for all instances of bar.Bar
--{-# NO_POSITIVITY_CHECK #-}
data eqTypes (u : univs) (w : world) (T1 T2 : Term) : Set₁
--{-# TERMINATING #-}
eqInType : (u : univs) (w : world) {T1 T2 : Term} → (eqTypes u w T1 T2) → per
\end{code}


Equality between type is defined as the following inductive definition


\begin{code}
data eqTypes u w T1 T2 where
  EQTNAT : T1 ⇛ NAT at w → T2 ⇛ NAT at w → eqTypes u w T1 T2
  EQTQNAT : T1 ⇛ QNAT at w → T2 ⇛ QNAT at w → eqTypes u w T1 T2
  EQTLT : (a1 a2 b1 b2 : Term)
    → T1 ⇛ (LT a1 b1) at w
    → T2 ⇛ (LT a2 b2) at w
    → strongMonEq w a1 a2
    → strongMonEq w b1 b2
    → eqTypes u w T1 T2
  EQTQLT : (a1 a2 b1 b2 : Term)
    → T1 ⇛ (QLT a1 b1) at w
    → T2 ⇛ (QLT a2 b2) at w
    → weakMonEq w a1 a2
    → weakMonEq w b1 b2
    → eqTypes u w T1 T2
  EQTFREE : T1 ⇛ FREE at w → T2 ⇛ FREE at w → eqTypes u w T1 T2
  EQTPI : (A1 B1 A2 B2 : Term)
    → T1 ⇛ (PI A1 B1) at w
    → T2 ⇛ (PI A2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTSUM : (A1 B1 A2 B2 : Term)
    → T1 ⇛ (SUM A1 B1) at w
    → T2 ⇛ (SUM A2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTSET : (A1 B1 A2 B2 : Term)
    → T1 ⇛ (SET A1 B1) at w
    → T2 ⇛ (SET A2 B2) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTEQ : (a1 b1 a2 b2 A B : Term)
    → T1 ⇛ (EQ a1 a2 A) at w
    → T2 ⇛ (EQ b1 b2 B) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A B))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (eqt1 : allW w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
    → (eqt2 : allW w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
    → eqTypes u w T1 T2
  EQTUNION : (A1 B1 A2 B2 : Term)
    → T1 ⇛ (UNION A1 B1) at w
    → T2 ⇛ (UNION A2 B2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtB : allW w (λ w' _ → eqTypes u w' B1 B2))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (extb : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
    → eqTypes u w T1 T2
  EQTSQUASH : (A1 A2 : Term)
    → T1 ⇛ (TSQUASH A1) at w
    → T2 ⇛ (TSQUASH A2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2
{--  EQTDUM : (A1 A2 : Term)
    → T1 ⇛ (DUM A1) at w
    → T2 ⇛ (DUM A2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2--}
  EQFFDEFS : (A1 A2 x1 x2 : Term)
    → T1 ⇛ (FFDEFS A1 x1) at w
    → T2 ⇛ (FFDEFS A2 x2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (eqx : allW w (λ w' e → eqInType u w' (eqtA w' e) x1 x2))
    → eqTypes u w T1 T2
  EQTUNIV : proj₁ (proj₂ u) w T1 T2 → eqTypes u w T1 T2
  EQTBAR : inbar w (λ w' _ → eqTypes u w' T1 T2) → eqTypes u w T1 T2
\end{code}


Equality in types is defined as the following recursive function.


\begin{code}
PIeq : (eqa : per) (eqb : (a b : Term) → eqa a b → per) → per
PIeq eqa eqb f g = (a b : Term) → (e : eqa a b) → eqb a b e (APPLY f a) (APPLY g b)


SUMeq : (eqa : per) (eqb : (a b : Term) → eqa a b → per) → wper
SUMeq eqa eqb w f g =
  Σ Term (λ a1 → Σ Term (λ a2 → Σ Term (λ b1 → Σ Term (λ b2 →
    Σ (eqa a1 a2) (λ ea →
    f ⇛ (PAIR a1 b1) at w
    × g ⇛ (PAIR a2 b2) at w
    × eqb a1 a2 ea b1 b2)))))


SETeq : (eqa : per) (eqb : (a b : Term) → eqa a b → per) → per
SETeq eqa eqb f g = Σ Term (λ b → Σ (eqa f g) (λ ea → eqb f g ea b b))


EQeq : (a1 a2 : Term) (eqa : per) → wper
EQeq a1 a2 eqa w t1 t2 =
  t1 ⇛ AX at w × t2 ⇛ AX at w × eqa a1 a2


UNIONeq : (eqa eqb : per) → wper
UNIONeq eqa eqb w t1 t2  =
  Σ Term (λ a → Σ Term (λ b →
    (t1 ⇛ (INL a) at w × t2 ⇛ (INL b) at w × eqa a b)
    ⊎
    (t1 ⇛ (INR a) at w × t2 ⇛ (INR b) at w × eqb a b)))


TSQUASHeq : (eqa : per) → wper
TSQUASHeq eqa w t1 t2  =
  Σ Term (λ a1 → Σ Term (λ a2 →
     (t1 ∼ a1 at w) × (t2 ∼ a2 at w) × (t1 ≈ t2 at w)
     × eqa a1 a2))

FFDEFSeq : Term → (eqa : per) → wper
FFDEFSeq x1 eqa w t1 t2 =
  Σ Term (λ x →
   (t1 ⇛ AX at w) × (t2 ⇛ AX at w)
   × eqa x1 x × nodefs x)


{-# TERMINATING #-}
--{-# INLINE inOpenBar' #-}
eqInType _ w (EQTNAT _ _) t1 t2 = inbar w (λ w' _ → strongMonEq w' t1 t2)
eqInType _ w (EQTQNAT _ _) t1 t2 = inbar w (λ w' _ → weakMonEq w' t1 t2)
eqInType _ w (EQTLT a1 _ b1 _ _ _ _ _) t1 t2 = inbar w (λ w' _ → lift-<NUM-pair w' a1 b1)
eqInType _ w (EQTQLT a1 _ b1 _ _ _ _ _) t1 t2 = inbar w (λ w' _ → lift-<NUM-pair w' a1 b1)
eqInType _ w (EQTFREE _ _) t1 t2 = inbar w (λ w' _ → ⇛to-same-CS w' t1 t2)
eqInType u w (EQTPI _ _ _ _ _ _ eqta eqtb exta extb) f1 f2 =
  inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f1 f2)
eqInType u w (EQTSUM _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  inbar w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' t1 t2)
eqInType u w (EQTSET _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  inbar w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) t1 t2)
eqInType u w (EQTEQ a1 _ a2 _ _ _ _ _ eqtA exta eqt1 eqt2) t1 t2 =
  inbar w (λ w' e → EQeq a1 a2 (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTUNION _ _ _ _ _ _ eqtA eqtB exta extb) t1 t2 =
  inbar w (λ w' e → UNIONeq (eqInType u w' (eqtA w' e)) (eqInType u w' (eqtB w' e)) w' t1 t2)
eqInType u w (EQTSQUASH _ _ _ _ eqtA exta) t1 t2 =
  inbar w (λ w' e → TSQUASHeq (eqInType u w' (eqtA w' e)) w' t1 t2)
--eqInType u w (EQTDUM _ _ _ _ eqtA exta) t1 t2 = Lift {0ℓ} 1ℓ ⊤
eqInType u w (EQFFDEFS _ _ x1 _ _ _ eqtA exta _) t1 t2 =
  inbar w (λ w' e → FFDEFSeq x1 (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTUNIV _) T1 T2 = proj₂ (proj₂ u) w T1 T2
eqInType u w (EQTBAR f) t1 t2 =
  inbar' w f (λ w' _ (x : eqTypes u w' _ _) → eqInType u w' x t1 t2)
  {-- This is an unfolding of the above, as agda doesn't like the above --}
{--  allW w (λ w0 e0 →
           let p  = f w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 → (z : w3 ≽ w) → eqInType u w3 (q w3 (extTrans e3 e2) z) t1 t2)))--}
\end{code}


We finally close the construction as follows:


\begin{code}
-- Two level-m universes are equal if they compute to (UNIV m)
eqUnivi : (m : ℕ) → wper
eqUnivi m w T1 T2 = inbar w (λ w' _ → T1 ⇛ (UNIV m) at w' × T2 ⇛ (UNIV m) at w')

-- Two terms are equal in universe m if they are equal according to eqTypes
eqInUnivi : (m : ℕ) → wper
eqInUnivi 0 = λ _ _ _ → Lift {0ℓ} 1ℓ ⊥
eqInUnivi (suc m) w T1 T2 =
  inbar w (λ w' _ → eqTypes (m , (eqUnivi m , eqInUnivi m)) w' T1 T2 {-- ⊎ eqInUnivi m w' T1 T2--})
-- To have this ⊎ we need a way to lift types in eqTypes, so that types equal at level 'n' can be equal
-- as types in lower universes, and then lifted up to being equal as types in 'n' again
-- The type system probably isn't transitive without that.

--- Add an explicit level-lifting constructor to the type system
uni : ℕ → univs
uni n = (n , (eqUnivi n , eqInUnivi n))

TEQ : Set₂
TEQ = (w : world) (T1 T2 : Term) → Set₁

EQT : Set₂
EQT = (w : world) (T a b : Term) → Set₁

-- Finally, the 'equal types' and 'equal in types' relations
equalTypes : (u : ℕ) → TEQ
equalTypes u = eqTypes (uni u)

equalInType : (u : ℕ) (w : world) (T : Term) → per
equalInType u w T a b = Σ (equalTypes u w T T) (λ p → eqInType (uni u) w p a b)
\end{code}


\begin{code}
eqtypes : TEQ
eqtypes w T1 T2 = Σ ℕ (λ u → equalTypes u w T1 T2)

eqintype : EQT
eqintype w T a b = Σ ℕ (λ u → equalInType u w T a b)

{--wfinhN1L : (j : ℕ) → wfInh (inhN1L j)
wfinhN1L j = ≤-refl

wfinhN2L : (j : ℕ) → wfInh (inhN2L j)
wfinhN2L j = (n≤1+n _)--}


¬s≤ : (j : ℕ) → ¬ suc j ≤ j
¬s≤ .(suc _) (_≤_.s≤s h) = ¬s≤ _ h

¬≡s : (j : ℕ) → ¬ j ≡ suc j
¬≡s 0 ()
¬≡s (suc j) ()

¬s≤0 : (j : ℕ) → ¬ suc j ≤ 0
¬s≤0 j ()

eq-pair : {a b : Level} {A : Set a} {B : Set b} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → ( a₁ , b₁ ) ≡ ( a₂ , b₂ )
eq-pair {a} {b} {A} {B} {a₁} {a₂} {b₁} {b₂} p q rewrite p | q = refl


≤-trans-≤-refl : {i j : ℕ} (c : i ≤ j) → ≤-trans c ≤-refl ≡ c
≤-trans-≤-refl {i} {j} c = ≤-irrelevant _ c


-- ---------------------------------
-- Type system
intype : (w : world) (T t : Term) → Set₁
intype w T t = eqintype w T t t

TEQsym : TEQ → Set₁
TEQsym τ = (w : world) (A B : Term) → τ w A B → τ w B A

TEQtrans : TEQ → Set₁
TEQtrans τ = (w : world) (A B C : Term) → τ w A B → τ w B C → τ w A C

EQTsym : EQT → Set₁
EQTsym σ = (w : world) (A a b : Term) → σ w A a b → σ w A b a

EQTtrans : EQT → Set₁
EQTtrans σ  = (w : world) (A a b c : Term) → σ w A a b → σ w A b c → σ w A a c

TSext : TEQ → EQT → Set₁
TSext τ σ = (w : world) (A B a b : Term) → τ w A B → σ w A a b → σ w B a b

record TS (τ : TEQ) (σ : EQT) : Set₁ where
  constructor mkts
  field
    tySym   : TEQsym τ
    tyTrans : TEQtrans τ
    eqSym   : EQTsym σ
    eqTrans : EQTtrans σ
    tsExt   : TSext τ σ


-- ---------------------------------
-- Sequents

record hypothesis : Set where
  constructor mkhyp
  field
    name : Var
    hyp  : Term

hypotheses : Set
hypotheses = List hypothesis

record sequent : Set where
  constructor mkseq
  field
    hyps  : hypotheses
    concl : Term

\end{code}
