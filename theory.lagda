\begin{code}
module theory where

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
open import world
\end{code}



We now provide an inductive-recursive realizability semantics of
OpenTT.


\begin{code}
-- PERs and world dependent PERs
per : Set₁
per = Term → Term → Set

wper : Set₁
wper = (I : Inh) (w : world) → per

-- eqTypes and eqInType provide meaning to types w.r.t. already interpreted universes,
-- given by univs (1st conjunct defines the equality between such universes, while the
-- second conjunct defines the equality in such universes)
univs : Set₁
univs = Σ ℕ (λ n → wper × wper)

-- equality between types (an inductive definition)
-- and equality in types (a recursive function)
data eqTypes (u : univs) (I : Inh) (w : world) (T1 T2 : Term) : Set
eqInType : (u : univs) (I : Inh) (w : world) {T1 T2 : Term} → (eqTypes u I w T1 T2) → per
\end{code}


Equality between type is defined as the following inductive definition


\begin{code}
data eqTypes u I w T1 T2 where
  EQTNAT : [ I ] T1 ⇛ NAT at w → [ I ] T2 ⇛ NAT at w → eqTypes u I w T1 T2
  EQTQNAT : [ I ] T1 ⇛ QNAT at w → [ I ] T2 ⇛ QNAT at w → eqTypes u I w T1 T2
  EQTLT : (a1 a2 b1 b2 : Term)
    → [ I ] T1 ⇛ (LT a1 b1) at w
    → [ I ] T2 ⇛ (LT a2 b2) at w
    → strongMonEq I w a1 a2
    → strongMonEq I w b1 b2
    → eqTypes u I w T1 T2
  EQTQLT : (a1 a2 b1 b2 : Term)
    → [ I ] T1 ⇛ (QLT a1 b1) at w
    → [ I ] T2 ⇛ (QLT a2 b2) at w
    → weakMonEq I w a1 a2
    → weakMonEq I w b1 b2
    → eqTypes u I w T1 T2
  EQTFREE : [ I ] T1 ⇛ FREE at w → [ I ] T2 ⇛ FREE at w → eqTypes u I w T1 T2
  EQTPI : (A1 B1 A2 B2 : Term)
    → [ I ] T1 ⇛ (PI A1 B1) at w
    → [ I ] T2 ⇛ (PI A2 B2) at w
    → (eqta : allW I w (λ w' _ → eqTypes u I w' A1 A2))
    → (eqtb : allW I w (λ w' e → ∀ a1 a2 → eqInType u I w' (eqta w' e) a1 a2
                         → eqTypes u I w' (sub a1 B1) (sub a2 B2)))
    → eqTypes u I w T1 T2
  EQTSUM : (A1 B1 A2 B2 : Term)
    → [ I ] T1 ⇛ (SUM A1 B1) at w
    → [ I ] T2 ⇛ (SUM A2 B2) at w
    → (eqta : allW I w (λ w' _ → eqTypes u I w' A1 A2))
    → (eqtb : allW I w (λ w' e → ∀ a1 a2 → eqInType u I w' (eqta w' e) a1 a2
                         → eqTypes u I w' (sub a1 B1) (sub a2 B2)))
    → eqTypes u I w T1 T2
  EQTSET : (A1 B1 A2 B2 : Term)
    → [ I ] T1 ⇛ (SET A1 B1) at w
    → [ I ] T2 ⇛ (SET A2 B2) at w
    → (eqta : allW I w (λ w' _ → eqTypes u I w' A1 A2))
    → (eqtb : allW I w (λ w' e → ∀ a1 a2 → eqInType u I w' (eqta w' e) a1 a2
                         → eqTypes u I w' (sub a1 B1) (sub a2 B2)))
    → eqTypes u I w T1 T2
  EQTEQ : (a1 b1 a2 b2 A B : Term)
    → [ I ] T1 ⇛ (EQ a1 a2 A) at w
    → [ I ] T2 ⇛ (EQ b1 b2 B) at w
    → (eqtA : allW I w (λ w' _ → eqTypes u I w' A B))
    → (eqt1 : allW I w (λ w' e → eqInType u I w' (eqtA w' e) a1 b1))
    → (eqt2 : allW I w (λ w' e → eqInType u I w' (eqtA w' e) a2 b2))
    → eqTypes u I w T1 T2
  EQTUNION : (A1 B1 A2 B2 : Term)
    → [ I ] T1 ⇛ (UNION A1 B1) at w
    → [ I ] T2 ⇛ (UNION A2 B2) at w
    → (eqtA : allW I w (λ w' _ → eqTypes u I w' A1 A2))
    → (eqtB : allW I w (λ w' _ → eqTypes u I w' B1 B2))
    → eqTypes u I w T1 T2
  EQTSQUASH : (A1 A2 : Term)
    → [ I ] T1 ⇛ (TSQUASH A1) at w
    → [ I ] T2 ⇛ (TSQUASH A2) at w
    → (eqtA : allW I w (λ w' _ → eqTypes u I w' A1 A2))
    → eqTypes u I w T1 T2
  EQFFDEFS : (A1 A2 x1 x2 : Term)
    → [ I ] T1 ⇛ (FFDEFS A1 x1) at w
    → [ I ] T2 ⇛ (FFDEFS A2 x2) at w
    → (eqtA : allW I w (λ w' _ → eqTypes u I w' A1 A2))
    → (eqx : allW I w (λ w' e → eqInType u I w' (eqtA w' e) x1 x1))
    → eqTypes u I w T1 T2
  EQTUNIV : proj₁ (proj₂ u) I w T1 T2 → eqTypes u I w T1 T2
  EQTBAR : inOpenBar I w (λ w' _ → eqTypes u I w' T1 T2) → eqTypes u I w T1 T2
  EQTLOWER : (A1 A2 : Term)
    → [ I ] T1 ⇛ (LOWER A1) at w
    → [ I ] T2 ⇛ (LOWER A2) at w
    → (eqt : allW I w (λ w' _ → eqTypes u (lower I) w' A1 A2))
    → eqTypes u I w T1 T2
\end{code}


Equality in types is defined as the following recursive function.


\begin{code}
eqInType _ I w (EQTNAT _ _) t1 t2 = inOpenBar I w (λ w' _ → strongMonEq I w' t1 t2)
eqInType _ I w (EQTQNAT _ _) t1 t2 = inOpenBar I w (λ w' _ → weakMonEq I w' t1 t2)
eqInType _ I w (EQTLT a1 _ b1 _ _ _ _ _) t1 t2 =
  inOpenBar I w (λ w' _ → Σ ℕ (λ n → Σ ℕ (λ m → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM m) at w' × n < m)))
eqInType _ I w (EQTQLT a1 _ b1 _ _ _ _ _) t1 t2 =
  inOpenBar I w (λ w' _ → Σ ℕ (λ n → Σ ℕ (λ m → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM m) at w' × n < m)))
eqInType _ I w (EQTFREE _ _) t1 t2 =
  inOpenBar I w (λ w' _ → Σ choiceSeqName (λ n → [ I ] t1 ⇛ (CS n) at w' × [ I ] t2 ⇛ (CS n) at w'))
eqInType u I w (EQTPI _ _ _ _ _ _ eqta eqtb) f1 f2 =
  inOpenBar I w (λ w' e → ∀ (a1 a2 : Term) (eqa : eqInType u I w' (eqta w' e) a1 a2)
                      → eqInType u I w' (eqtb w' e a1 a2 eqa) (APPLY f1 a1) (APPLY f2 a2))
eqInType u I w (EQTSUM _ _ _ _ _ _ eqta eqtb) t1 t2 =
  inOpenBar I w (λ w' e → Σ Term (λ a1 → Σ Term (λ a2 → Σ Term (λ b1 → Σ Term (λ b2 →
                         Σ (eqInType u I w' (eqta w' e) a1 a2) (λ ea →
                         [ I ] t1 ⇛ (PAIR a1 b1) at w'
                         × [ I ] t2 ⇛ (PAIR a2 b2) at w'
                         × eqInType u I w' (eqtb w' e a1 a2 ea) b1 b2))))))
eqInType u I w (EQTSET _ _ _ _ _ _ eqta eqtb) t1 t2 =
  inOpenBar I w (λ w' e → Σ Term (λ b → Σ (eqInType u I w' (eqta w' e) t1 t2) (λ ea →
                         eqInType u I w' (eqtb w' e t1 t2 ea) b b)))
eqInType u I w (EQTEQ a1 b1 _ _ _ _ _ _ eqtA eqt1 eqt2) t1 t2 =
  inOpenBar I w (λ w' e → [ I ] t1 ⇛ AX at w' × [ I ] t2 ⇛ AX at w' × eqInType u I w' (eqtA w' e) a1 b1)
eqInType u I w (EQTUNION _ _ _ _ _ _ eqtA eqtB) t1 t2 =
  inOpenBar I w (λ w' e → Σ Term (λ a → Σ Term (λ b →
                 ([ I ] t1 ⇛ (INL a) at w' × [ I ] t2 ⇛ (INR b) at w' × eqInType u I w' (eqtA w' e) a b)
                 ⊎
                 ([ I ] t1 ⇛ (INR a) at w' × [ I ] t2 ⇛ (INR b) at w' × eqInType u I w' (eqtB w' e) a b))))
eqInType u I w (EQTSQUASH _ _ _ _ eqtA) t1 t2 =
  inOpenBar I w (λ w' e → Σ Term (λ a1 → Σ Term (λ a2 →
                 (t1 ∼ a1 at w') × (t2 ∼ a2 at w') × ([ I ] t1 ≈ t2 at w')
                 × eqInType u I w' (eqtA w' e) a1 a2)))
eqInType u I w (EQFFDEFS _ _ x1 _ _ _ eqtA _) t1 t2 =
  inOpenBar I w (λ w' e → Σ Term (λ x →
                ([ I ] t1 ⇛ AX at w') × ([ I ] t2 ⇛ AX at w')
                × eqInType u I w' (eqtA w' e) x1 x × nodefs x))
eqInType u I w (EQTUNIV _) T1 T2 = proj₂ (proj₂ u) I w T1 T2
eqInType u I w (EQTBAR f) t1 t2 =
  {-- inOpenBar' w f (λ w' _ (x : eqTypes u w' _ _) → eqInType u w' x t1 t2)--}
  {-- This is an unfolding of the above, as agda doesn't like the above --}
  allW I w (λ w0 e0 →
           let p  = f w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW I w1 (λ w2 e2 → allW I w2 (λ w3 e3 → eqInType u I w3 (q w3 (eTrans {I} e3 e2)) t1 t2)))
eqInType u I w (EQTLOWER _ _ _ _ eqt) t1 t2 =
  inOpenBar I w (λ w' e → eqInType u (lower I) w' (eqt w' e) t1 t2)
\end{code}


We finally close the construction as follows:


\begin{code}
-- Two level-m universes are equal if they compute to (UNIV m)
eqUnivi : (m : ℕ) → wper
eqUnivi m I w T1 T2 = inOpenBar I w (λ w' _ → [ I ] T1 ⇛ (UNIV m) at w' × [ I ] T2 ⇛ (UNIV m) at w')

-- Two terms are equal in universe m if they are equal according to eqTypes
eqInUnivi : (m : ℕ) → wper
eqInUnivi 0 I = λ _ _ _ → ⊥
eqInUnivi (suc m) I w T1 T2 = eqTypes (m , (eqUnivi m , eqInUnivi m)) I w T1 T2 ⊎ eqInUnivi m I w T1 T2

uni : ℕ → univs
uni n = (n , (eqUnivi n , eqInUnivi n))

TEQ : Set₁
TEQ = (w : world) (T1 T2 : Term) → Set

EQT : Set₁
EQT = (w : world) (T a b : Term) → Set

-- Finally, the 'equal types' and 'equal in types' relations
eqtypesI : (I : Inh) → TEQ
eqtypesI I w T1 T2 = Σ ℕ (λ n → eqTypes (uni n) I w T1 T2)

equalInType : (u : univs) (I : Inh) (w : world) (T : Term) → per
equalInType u I w T a b = Σ (eqTypes u I w T T) (λ p → eqInType u I w p a b)

eqintypeI : (I : Inh) → EQT
eqintypeI I w T a b = Σ ℕ (λ n → equalInType (uni n) I w T a b)
\end{code}


\begin{code}
eqintypeN : (m n : ℕ) → EQT
inhL : (m n : ℕ) → InhF m n
inhN : (m n : ℕ) → Inh


eqintypeN m 0 w T a b = ⊤
eqintypeN m n w T a b = eqintypeI (inhN m n) w T a b

inhL m 0 j c₁ c₂ w U = ⊤
inhL m (suc n) j c₁ c₂ w U with m≤n⇒m<n∨m≡n c₂
... | inj₁ p = inhL m n j c₁ (sucLeInj p) w U
... | inj₂ p = Σ Term (λ t → eqintypeN m n w U t t)

inhN m n = (m , n , inhL m n)

inhN1L : (n : ℕ) → Inh
inhN1L n = inhN n n -- That gives us 1 levels

inhN2L : (n : ℕ) → Inh
inhN2L n = inhN n (suc n) -- That gives us 2 levels


eqtypesN : (m n : ℕ) → TEQ
eqtypesN m n w T1 T2 = eqtypesI (inhN m n) w T1 T2

eqtypes : TEQ
eqtypes w T1 T2 = Σ ℕ (λ n → Σ ℕ (λ k → (j : ℕ) → j ≥ n → eqtypesN j (k + j) w T1 T2))

eqintype : EQT
eqintype w T a b = Σ ℕ (λ n → Σ ℕ (λ k → (j : ℕ) → j ≥ n → eqintypeN j (k + j) w T a b))
\end{code}
