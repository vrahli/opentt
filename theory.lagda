{-# OPTIONS --allow-unsolved-metas #-}

\begin{code}
module theory where

open import Level using (Level ; 0ℓ) renaming (suc to lsuc)
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
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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

postulate
  fext : Relation.Binary.PropositionalEquality.Extensionality 0ℓ (lsuc 0ℓ)
--  fext : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc 0ℓ)


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
    → (eqt : allW I w (λ w' _ → allI (lower I) (λ i → eqTypes u i w' A1 A2)))
    → eqTypes u I w T1 T2
  EQTSHRINK : (A1 A2 : Term)
    → [ I ] T1 ⇛ (SHRINK A1) at w
    → [ I ] T2 ⇛ (SHRINK A2) at w
    → (eqt : allW I w (λ w' _ → eqTypes u (shrink I) w' A1 A2))
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
  inOpenBar I w (λ w' _ → Σ csName (λ n → [ I ] t1 ⇛ (CS n) at w' × [ I ] t2 ⇛ (CS n) at w'))
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
           exW I w1 (λ w2 e2 → allW I w2 (λ w3 e3 → eqInType u I w3 (q w3 ([]≽-trans {I} e3 e2)) t1 t2)))
eqInType u I w (EQTLOWER _ _ _ _ eqt) t1 t2 =
  -- inOpenBar I w (λ w' e → allI≤ (lower I) (λ j c₁ c₂ i → eqInType u i w' (eqt w' e j c₁ c₂) t1 t2))
  inOpenBar I w (λ w' e → (j : ℕ) (c₁ : Inh.m I ≤ j) (c₂ : j ≤ Inh.n (lower I)) →
                   eqInType u (mkinh (Inh.m I) j (λ i c → Inh.f (lower I) i (≤-trans c c₂))) w' (eqt w' e j c₁ c₂) t1 t2)
eqInType u I w (EQTSHRINK _ _ _ _ eqt) t1 t2 =
  inOpenBar I w (λ w' e → eqInType u (shrink I) w' (eqt w' e) t1 t2)
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
equalTypes : (u : ℕ) → (I : Inh) → TEQ
equalTypes u = eqTypes (uni u)

equalInType : (u : ℕ) (I : Inh) (w : world) (T : Term) → per
equalInType u I w T a b = Σ (equalTypes u I w T T) (λ p → eqInType (uni u) I w p a b)
\end{code}


\begin{code}
eqintypeN : (u m n : ℕ) → EQT
inhL : (u m n : ℕ) → InhF n
inhN : (u m n : ℕ) → Inh


eqintypeN u m n w T a b = equalInType u (inhN u m n) w T a b

inhL u m 0 j c w T = ⊤
inhL u m (suc n) j c w T with m≤n⇒m<n∨m≡n c
... | inj₁ p = inhL u m n j (sucLeInj p) w T
... | inj₂ p = Σ Term (λ t → eqintypeN u m n w T t t)

inhN u m n = mkinh m n (inhL u m n)

inhN1L : (u n : ℕ) → Inh
inhN1L u n = inhN u n n -- That gives us 1 "low" level

{--inhN1H : (u n : ℕ) → Inh
inhN1H u n = inhN u (suc n) (suc n) -- That gives us 1 "high" level
--}

inhN2L : (u n : ℕ) → Inh
inhN2L u n = inhN u n (suc n) -- That gives us 2 "low" levels

{--inhN2H : (u n : ℕ) → Inh
inhN2H u n = inhN u (suc n) (suc (suc n)) -- That gives us 2 "high" levels
--}


eqtypesN : (u m n : ℕ) → TEQ
eqtypesN u m n w T1 T2 = equalTypes u (inhN u m n) w T1 T2

eqtypes : TEQ
eqtypes w T1 T2 = Σ ℕ (λ u → Σ ℕ (λ n → Σ ℕ (λ k → (j : ℕ) → j ≥ n → eqtypesN u j (k + j) w T1 T2)))

eqintype : EQT
eqintype w T a b = Σ ℕ (λ u → Σ ℕ (λ n → Σ ℕ (λ k → (j : ℕ) → j ≥ n → eqintypeN u j (k + j) w T a b)))

{--wfinhN1L : (j : ℕ) → wfInh (inhN1L j)
wfinhN1L j = ≤-refl

wfinhN2L : (j : ℕ) → wfInh (inhN2L j)
wfinhN2L j = (n≤1+n _)--}


sucNotLe : (j : ℕ) → ¬ suc j ≤ j
sucNotLe .(suc _) (_≤_.s≤s h) = sucNotLe _ h

eq-pair : {a b : Level} {A : Set a} {B : Set b} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → ( a₁ , b₁ ) ≡ ( a₂ , b₂ )
eq-pair {a} {b} {A} {B} {a₁} {a₂} {b₁} {b₂} p q rewrite p | q = refl


inhN1Leq1 : (u n j : ℕ) (c : j ≤ n) (w : world) (t : Term)
          → inhL u n n j c w t ≡ inhL u n (suc n) j (≤-trans c (n≤1+n _)) w t
inhN1Leq1 u n j c w t with m≤n⇒m<n∨m≡n (≤-trans c (n≤1+n _))
... | inj₁ x = subst (λ z → inhL u n n j z w t ≡ inhL u n n j (sucLeInj x) w t) (≤-irrelevant _ c) refl
... | inj₂ x rewrite x = ⊥-elim (sucNotLe _ c)


inhN1Leq : (u n : ℕ) → inhL u n n ≡ λ j c → inhL u n (suc n) j (≤-trans c (n≤1+n _))
inhN1Leq u n = fext (λ j → fext (λ c → fext (λ w → fext (λ t → inhN1Leq1 u n j c w t))))

inhN1L≡lower-inhN2L : (u n : ℕ) → inhN1L u n ≡ lower (inhN2L u n) --(j , (λ m c → snd (inhNs j) m (≤-trans c (n≤1+n j))))
inhN1L≡lower-inhN2L u n rewrite inhN1Leq u n = refl

eq-mkinh : {m n : ℕ} {f g : InhF n} → f ≡ g → mkinh m n f ≡ mkinh m n g
eq-mkinh {m} {n} {f} {g} e rewrite e = refl

≤-trans-≤-refl : {i j : ℕ} (c : i ≤ j) → ≤-trans c ≤-refl ≡ c
≤-trans-≤-refl {i} {j} c = ≤-irrelevant _ c

inhN1Leq2 : (u j : ℕ) → inhN1L u j ≡ mkinh (Inh.m (inhN1L u j)) j (λ i c → Inh.f (inhN1L u j) i (≤-trans c ≤-refl))
inhN1Leq2 u j =
  eq-mkinh (fext (λ j0 → fext (λ c → fext (λ w → fext (λ t →
    subst (λ x → inhL u j j j0 c w t ≡ Inh.f (inhN1L u j) j0 x w t) (sym (≤-trans-≤-refl c)) refl)))))

allI-inhN1L : {u j : ℕ} {f : Inh → Set} → allI (inhN1L u j) f → f (inhN1L u j)
allI-inhN1L {u} {j} {f} h rewrite inhN1Leq2 u j = h j ≤-refl ≤-refl

allI-lower-inhN2L : {u j : ℕ} {f : Inh → Set} → allI (lower (inhN2L u j)) f → f (inhN1L u j)
allI-lower-inhN2L {u} {j} {f} h =
  allI-inhN1L {u} {j} {f} (subst (λ x → allI x f) (sym (inhN1L≡lower-inhN2L u j)) h )

{--inhN2LeqinhN1L : (u j i : ℕ) (c₁ : j ≤ i) (c₂ : i ≤ j)
                 → inhL u j j i c₁ c₂ ≡ inhL u j (suc j) i c₁ (≤-trans c₂ (n≤1+n j))
inhN2LeqinhN1L u j i c₁ c₂ rewrite inhLeq u j = refl--}


{--ext2LimpliesExt1L : (j : ℕ) (w1 w2 : world) → [ inhN2L j ] w2 ⪰ w1 → [ inhN1L j ] w2 ⪰ w1
ext2LimpliesExt1L j w1 w2 h i =
  λ c₁ c₂ → let h1 = h i c₁ (≤-trans c₂ (n≤1+n _)) in
    subst (λ x → ⟨ x ⟩ w2 ⪰ w1) (sym (inhN2LeqinhN1L j i c₁ c₂)) h1--}

{--lower-inhN2H-inhL2 : (u n : ℕ) (j : ℕ) (c : j ≤ suc n) (w : world) (T : Term)
                     → inhL u n (suc n) j c w T ≡ inhL u (suc n) (suc (suc n)) j (≤-trans c (n≤1+n _)) w T
lower-inhN2H-inhL2 u n j c w T with m≤n⇒m<n∨m≡n c
... | inj₁ p with m≤n⇒m<n∨m≡n (≤-trans c (_≤_.s≤s (≤-step (≤-reflexive refl))))
...             | inj₁ q with m≤n⇒m<n∨m≡n (sucLeInj q)
...                         | inj₁ r rewrite ≤-irrelevant p r = refl
...                         | inj₂ r rewrite r = ⊥-elim (sucNotLe _ p)
lower-inhN2H-inhL2 u n j c w T | inj₁ p | inj₂ q rewrite q = ⊥-elim (sucNotLe _ c)
lower-inhN2H-inhL2 u n j c w T | inj₂ p with m≤n⇒m<n∨m≡n (≤-trans c (_≤_.s≤s (≤-step (≤-reflexive refl))))
... | inj₁ q with m≤n⇒m<n∨m≡n (sucLeInj q)
...             | inj₁ r rewrite p = ⊥-elim (sucNotLe _ r)
...             | inj₂ r = refl
lower-inhN2H-inhL2 u n j c w T | inj₂ p | inj₂ q rewrite p = ⊥-elim (1+n≢n (sym q))--}

{--lower-inhN2H-inhL : (u n : ℕ) → inhL u n (suc n) ≡ λ j c → inhL u (suc n) (suc (suc n)) j (≤-trans c (n≤1+n _))
lower-inhN2H-inhL u n = fext (λ j → fext (λ c → fext (λ w → fext (λ t → lower-inhN2H-inhL2 u n j c w t))))
--}

{--lower-inhN2H : (u j : ℕ) → lower (inhN2H u j) ≡ inhN2L u j
lower-inhN2H u j =
  eq-pair refl (Inverse.f Σ-≡,≡↔≡ (refl , sym (lower-inhN2H-inhL u j)))
--}


-- ---------------------------------
-- Type system
intype : (w : world) (T t : Term) → Set
intype w T t = eqintype w T t t

{--inh : InhW
inh w T = Σ Term (λ t → intype w T t)

_⪰·_ : (w2 : world) (w1 : world) → Set
w2 ⪰· w1 = ⟨ inh ⟩ w2 ⪰ w1--}

TEQsym : TEQ → Set
TEQsym τ = (w : world) (A B : Term) → τ w A B → τ w B A

TEQtrans : TEQ → Set
TEQtrans τ = (w : world) (A B C : Term) → τ w A B → τ w B C → τ w A C

EQTsym : EQT → Set
EQTsym σ = (w : world) (A a b : Term) → σ w A a b → σ w A b a

EQTtrans : EQT → Set
EQTtrans σ  = (w : world) (A a b c : Term) → σ w A a b → σ w A b c → σ w A a c

TSext : TEQ → EQT → Set
TSext τ σ = (w : world) (A B a b : Term) → τ w A B → σ w A a b → σ w B a b

record TS (τ : TEQ) (σ : EQT) : Set where
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
