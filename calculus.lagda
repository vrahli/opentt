\begin{code}
module calculus where

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
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
\end{code}


\begin{code}
postulate
  choiceSeqName : Set
  freshName : (l : List choiceSeqName) → Σ choiceSeqName (λ name → ¬ (name ∈ l))

Var : Set
Var = ℕ

data Term : Set where
  -- Variables
  VAR : Var → Term
  -- Numbers
  NAT : Term
  QNAT : Term
  LT : Term → Term → Term
  QLT : Term → Term → Term
  NUM : ℕ → Term
  -- Products
  PI :  Term → Term → Term
  LAMBDA : Term → Term
  APPLY : Term → Term → Term
  -- Sums
  SUM : Term → Term → Term
  PAIR : Term → Term → Term
  SPREAD : Term → Term → Term
  -- Sets --- they don't have constructors/destructors
  SET : Term → Term → Term
  -- Disjoint unions
  UNION : Term → Term → Term
  INL : Term → Term
  INR : Term → Term
  DECIDE : Term → Term → Term → Term
  -- Equality
  EQ : Term → Term → Term → Term
  AX : Term
  -- Choice sequences
  FREE : Term
  CS : choiceSeqName → Term
  -- Time squashing
  TSQUASH : Term → Term
  -- Free from definitions
  FFDEFS : Term → Term → Term
  -- Universes
  UNIV : ℕ → Term
  --
  LOWER : Term -> Term

isValue : Term → Set
isValue (VAR _) = ⊥
isValue NAT = ⊤
isValue QNAT = ⊤
isValue (LT _ _) = ⊥
isValue (QLT _ _) = ⊥
isValue (NUM _) = ⊤
isValue (PI _ _) = ⊤
isValue (LAMBDA _) = ⊤
isValue (APPLY _ _) = ⊥
isValue (SUM _ _) = ⊤
isValue (PAIR _ _) = ⊤
isValue (SPREAD _ _) = ⊥
isValue (SET _ _) = ⊤
isValue (UNION _ _) = ⊤
isValue (INL _) = ⊤
isValue (INR _) = ⊤
isValue (DECIDE _ _ _) = ⊥
isValue (EQ _ _ _) = ⊤
isValue AX = ⊤
isValue FREE = ⊤
isValue (CS _) = ⊤
isValue (TSQUASH _) = ⊤
isValue (FFDEFS _ _) = ⊤
isValue (UNIV _) = ⊤
isValue (LOWER _) = ⊤

{--
-- all variables
vars : Term → List Var
vars (VAR x) = [ x ]
vars NAT = []
vars QNAT = []
vars (LT t t₁) =  vars t ++ vars t₁
vars (QLT t t₁) = vars t ++ vars t₁
vars (NUM x) = []
vars (PI t x t₁) = x ∷ vars t ++ vars t₁
vars (LAMBDA x t) = x ∷ vars t
vars (APPLY t t₁) = vars t ++ vars t₁
vars (SUM t x t₁) = x ∷ vars t ++ vars t₁
vars (PAIR t t₁) = vars t ++ vars t₁
vars (SPREAD t x x₁ t₁) = x ∷ x₁ ∷ vars t ++ vars t₁
vars (SET t x t₁) = x ∷ vars t ++ vars t₁
vars (UNION t t₁) = vars t ++ vars t₁
vars (INL t) = vars t
vars (INR t) = vars t
vars (DECIDE t x₁ t₁ x₂ t₂) = x₁ ∷ x₂ ∷ vars t ++ vars t₁ ++ vars t₂
vars (EQ t t₁ t₂) = vars t ++ vars t₁ ++ vars t₂
vars AX = []
vars FREE = []
vars (CS x) = []
vars (TSQUASH t) = vars t
vars (FFDEFS t t₁) = vars t ++ vars t₁
vars (UNIV x) = []
vars (LOWER t) = vars t

diff : (v : Var) → Pred Var 0ℓ
diff v x = ¬ (v ≡ x)

decDiff : (v : Var) → Decidable (diff v)
decDiff v x = {!!}

remove : Var → List Var -> List Var
remove v l = filter (decDiff v) l
--}

lowerVars : List Var → List Var
lowerVars [] = []
lowerVars (0 ∷ l) = lowerVars l
lowerVars (suc n ∷ l) = n ∷ lowerVars l

-- free variables
fvars : Term → List Var
fvars (VAR x)          = [ x ]
fvars NAT              = []
fvars QNAT             = []
fvars (LT t t₁)        = fvars t ++ fvars t₁
fvars (QLT t t₁)       = fvars t ++ fvars t₁
fvars (NUM x)          = []
fvars (PI t t₁)        = fvars t ++ lowerVars (fvars t₁)
fvars (LAMBDA t)       = lowerVars (fvars t)
fvars (APPLY t t₁)     = fvars t ++ fvars t₁
fvars (SUM t t₁)       = fvars t ++ lowerVars (fvars t₁)
fvars (PAIR t t₁)      = fvars t ++ fvars t₁
fvars (SPREAD t t₁)    = fvars t ++ lowerVars (lowerVars (fvars t₁))
fvars (SET t t₁)       = fvars t ++ lowerVars (fvars t₁)
fvars (UNION t t₁)     = fvars t ++ fvars t₁
fvars (INL t)          = fvars t
fvars (INR t)          = fvars t
fvars (DECIDE t t₁ t₂) = fvars t ++ lowerVars (fvars t₁) ++ lowerVars (fvars t₂)
fvars (EQ t t₁ t₂)     = fvars t ++ fvars t₁ ++ fvars t₂
fvars AX               = []
fvars FREE             = []
fvars (CS x)           = []
fvars (TSQUASH t)      = fvars t
fvars (FFDEFS t t₁)    = fvars t ++ fvars t₁
fvars (UNIV x)         = []
fvars (LOWER t)        = fvars t


_#_ : (v : Var) (t : Term) → Set
v # t = ¬ (v ∈ fvars t)

-- closed expression
#_ : (t : Term) → Set
# t = (v : Var) → v # t

shiftUp : ℕ → Term → Term
shiftUp c (VAR x) with x <? c
... | yes _ = VAR x
... | no _ = VAR (suc x)
shiftUp c NAT = NAT
shiftUp c QNAT = QNAT
shiftUp c (LT t t₁) = LT (shiftUp c t) (shiftUp c t₁)
shiftUp c (QLT t t₁) = QLT (shiftUp c t) (shiftUp c t₁)
shiftUp c (NUM x) = NUM x
shiftUp c (PI t t₁) = PI (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (LAMBDA t) = LAMBDA (shiftUp (suc c) t)
shiftUp c (APPLY t t₁) = APPLY (shiftUp c t) (shiftUp c t₁)
shiftUp c (SUM t t₁) = SUM (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (PAIR t t₁) = PAIR (shiftUp c t) (shiftUp c t₁)
shiftUp c (SPREAD t t₁) = SPREAD (shiftUp c t) (shiftUp (suc (suc c)) t₁)
shiftUp c (SET t t₁) = SET (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (UNION t t₁) = UNION (shiftUp c t) (shiftUp c t₁)
shiftUp c (INL t) = INL (shiftUp c t)
shiftUp c (INR t) = INR (shiftUp c t)
shiftUp c (DECIDE t t₁ t₂) = DECIDE (shiftUp c t) (shiftUp (suc c) t₁) (shiftUp (suc c) t₂)
shiftUp c (EQ t t₁ t₂) = EQ (shiftUp c t) (shiftUp c t₁) (shiftUp c t₂)
shiftUp c AX = AX
shiftUp c FREE = FREE
shiftUp c (CS x) = CS x
shiftUp c (TSQUASH t) = TSQUASH (shiftUp c t)
shiftUp c (FFDEFS t t₁) = FFDEFS (shiftUp c t) (shiftUp c t₁)
shiftUp c (UNIV x) = UNIV x
shiftUp c (LOWER t) = LOWER (shiftUp c t)

shiftDown : ℕ → Term → Term
shiftDown c (VAR 0) = VAR 0
shiftDown c (VAR (suc x)) with suc x <? c
... | yes _ = VAR (suc x)
... | no _ = VAR x
shiftDown c NAT = NAT
shiftDown c QNAT = QNAT
shiftDown c (LT t t₁) = LT (shiftDown c t) (shiftDown c t₁)
shiftDown c (QLT t t₁) = QLT (shiftDown c t) (shiftDown c t₁)
shiftDown c (NUM x) = NUM x
shiftDown c (PI t t₁) = PI (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (LAMBDA t) = LAMBDA (shiftDown (suc c) t)
shiftDown c (APPLY t t₁) = APPLY (shiftDown c t) (shiftDown c t₁)
shiftDown c (SUM t t₁) = SUM (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (PAIR t t₁) = PAIR (shiftDown c t) (shiftDown c t₁)
shiftDown c (SPREAD t t₁) = SPREAD (shiftDown c t) (shiftDown (suc (suc c)) t₁)
shiftDown c (SET t t₁) = SET (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (UNION t t₁) = UNION (shiftDown c t) (shiftDown c t₁)
shiftDown c (INL t) = INL (shiftDown c t)
shiftDown c (INR t) = INR (shiftDown c t)
shiftDown c (DECIDE t t₁ t₂) = DECIDE (shiftDown c t) (shiftDown (suc c) t₁) (shiftDown (suc c) t₂)
shiftDown c (EQ t t₁ t₂) = EQ (shiftDown c t) (shiftDown c t₁) (shiftDown c t₂)
shiftDown c AX = AX
shiftDown c FREE = FREE
shiftDown c (CS x) = CS x
shiftDown c (TSQUASH t) = TSQUASH (shiftDown c t)
shiftDown c (FFDEFS t t₁) = FFDEFS (shiftDown c t) (shiftDown c t₁)
shiftDown c (UNIV x) = UNIV x
shiftDown c (LOWER t) = LOWER (shiftDown c t)

subv : Var → Term → Term → Term
subv v t (VAR x) with x ≟ v
... | yes _ = t
... | no _ = VAR x
subv v t NAT = NAT
subv v t QNAT = QNAT
subv v t (LT u u₁) = LT (subv v t u) (subv v t u₁)
subv v t (QLT u u₁) = QLT (subv v t u) (subv v t u₁)
subv v t (NUM x) = NUM x
subv v t (PI u u₁) =  PI (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (LAMBDA u) =  LAMBDA (subv (suc v) (shiftUp 0 t) u)
subv v t (APPLY u u₁) = APPLY (subv v t u) (subv v t u₁)
subv v t (SUM u u₁) = SUM (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (PAIR u u₁) = PAIR (subv v t u) (subv v t u₁)
subv v t (SPREAD u u₁) = SPREAD (subv v t u) (subv (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subv v t (SET u u₁) = SET (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (UNION u u₁) = UNION (subv v t u) (subv v t u₁)
subv v t (INL u) = INL (subv v t u)
subv v t (INR u) = INR (subv v t u)
subv v t (DECIDE u u₁ u₂) = DECIDE (subv v t u) (subv (suc v) (shiftUp 0 t) u₁) (subv (suc v) (shiftUp 0 t) u₂)
subv v t (EQ u u₁ u₂) = EQ (subv v t u) (subv v t u₁) (subv v t u₂)
subv v t AX = AX
subv v t FREE = FREE
subv v t (CS x) = CS x
subv v t (TSQUASH u) = TSQUASH (subv v t u)
subv v t (FFDEFS u u₁) = FFDEFS (subv v t u) (subv v t u₁)
subv v t (UNIV x) = UNIV x
subv v t (LOWER u) = LOWER (subv v t u)

-- substitute '0' for 't' in 'u'
sub : Term → Term → Term
sub t u = shiftDown 0 (subv 0 (shiftUp 0 t) u)

notInAppVars1 : {v : Var} {l k : List Var} → ¬ v ∈ l ++ k → ¬ v ∈ l
notInAppVars1 {v} {l} {k} n i =  ⊥-elim (n (∈-++⁺ˡ i))

notInAppVars2 : {v : Var} {l k : List Var} → ¬ v ∈ l ++ k → ¬ v ∈ k
notInAppVars2 {v} {l} {k} n i =  ⊥-elim (n (∈-++⁺ʳ l i))

lowerVarsApp : (l k : List Var) → lowerVars (l ++ k) ≡ lowerVars l ++ lowerVars k
lowerVarsApp [] k = refl
lowerVarsApp (0 ∷ l) k = lowerVarsApp l k
lowerVarsApp (suc x ∷ l) k rewrite lowerVarsApp l k = refl

inLowerVars : (v : Var) (l : List Var) → (suc v) ∈ l → v ∈ lowerVars l
inLowerVars v (x ∷ l) (here px) rewrite (sym px) = here refl
inLowerVars v (0 ∷ l) (there i) = inLowerVars v l i
inLowerVars v (suc x ∷ l) (there i) = there (inLowerVars v l i)

subvNotIn : (v : Var) (t u : Term) → ¬ (v ∈ fvars u) → subv v t u ≡ u
subvNotIn v t (VAR x) n with x ≟ v
... | yes p =  ⊥-elim (n (here (sym p)))
... | no p = refl
subvNotIn v t NAT n = refl
subvNotIn v t QNAT n = refl
subvNotIn v t (LT u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (QLT u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (NUM x) n = refl
subvNotIn v t (PI u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (LAMBDA u) n
  rewrite subvNotIn (suc v) (shiftUp 0 t) u (λ j → ⊥-elim (n (inLowerVars _ _ j))) = refl
subvNotIn v t (APPLY u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (SUM u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (PAIR u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (SPREAD u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ (inLowerVars _ _ j)))) = refl
subvNotIn v t (SET u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (UNION u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (INL u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (INR u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (DECIDE u u₁ u₂) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim
            (notInAppVars1 {v} {lowerVars (fvars u₁)} {_}
               (notInAppVars2 {v} {fvars u} {_} n)
               (inLowerVars _ _ j)))
  rewrite subvNotIn (suc v) (shiftUp 0 t) u₂ (λ j → ⊥-elim
            (notInAppVars2 {v} {lowerVars (fvars u₁)} {_}
               (notInAppVars2 {v} {fvars u} {_} n)
               (inLowerVars _ _ j))) = refl
subvNotIn v t (EQ u u₁ u₂) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
  rewrite subvNotIn v t u₂ (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)) = refl
subvNotIn v t AX n = refl
subvNotIn v t FREE n = refl
subvNotIn v t (CS x) n = refl
subvNotIn v t (TSQUASH u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (FFDEFS u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (UNIV x) n = refl
subvNotIn v t (LOWER u) n
  rewrite subvNotIn v t u n = refl

sucLeInj : {a b : ℕ} → suc a ≤ suc b → a ≤ b
sucLeInj {a} {b} (_≤_.s≤s i) = i

impLeNotApp1 : (v : Var) (l k : List Var) → ((w : Var) → v ≤ w → ¬ (w ∈ l ++ k)) → ((w : Var) → v ≤ w → ¬ (w ∈ l))
impLeNotApp1 v l k i w j h = i w j (∈-++⁺ˡ h)

impLeNotApp2 : (v : Var) (l k : List Var) → ((w : Var) → v ≤ w → ¬ (w ∈ l ++ k)) → ((w : Var) → v ≤ w → ¬ (w ∈ k))
impLeNotApp2 v l k i w j h = i w j (∈-++⁺ʳ l h)

impLeNotLower : (v : Var) (l : List Var) → ((w : Var) → v ≤ w → ¬ (w ∈ lowerVars l)) → ((w : Var) → suc v ≤ w → ¬ (w ∈ l))
impLeNotLower v l i (suc w) j h = i w (sucLeInj j) (inLowerVars _ _ h)

shiftDownTrivial : (v : Var) (u : Term) → ((w : Var) → v ≤ w → w # u) → shiftDown v u ≡ u
shiftDownTrivial v (VAR 0) i = refl
shiftDownTrivial v (VAR (suc x)) i with suc x <? v
... | yes z = refl
... | no z = ⊥-elim (i (suc x) (sucLeInj (≰⇒> z)) (here refl))
shiftDownTrivial v NAT i = refl
shiftDownTrivial v QNAT i = refl
shiftDownTrivial v (LT u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (QLT u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (NUM x) i = refl
shiftDownTrivial v (PI u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftDownTrivial v (LAMBDA u) i
  rewrite shiftDownTrivial (suc v) u (impLeNotLower _ _ i) = refl
shiftDownTrivial v (APPLY u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (SUM u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftDownTrivial v (PAIR u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (SPREAD u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl
shiftDownTrivial v (SET u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftDownTrivial v (UNION u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (INL u) i
  rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (INR u) i
  rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (DECIDE u u₁ u₂) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite lowerVarsApp (fvars u₁) (fvars u₂)
  rewrite shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp1 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i)))
  rewrite shiftDownTrivial (suc v) u₂ (impLeNotLower _ _ (impLeNotApp2 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i))) = refl
shiftDownTrivial v (EQ u u₁ u₂) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
  rewrite shiftDownTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
shiftDownTrivial v AX i = refl
shiftDownTrivial v FREE i = refl
shiftDownTrivial v (CS x) i = refl
shiftDownTrivial v (TSQUASH u) i
  rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (FFDEFS u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (UNIV x) i = refl
shiftDownTrivial v (LOWER u) i
  rewrite shiftDownTrivial v u i = refl

shiftUpTrivial : (v : Var) (u : Term) → ((w : Var) → v ≤ w → w # u) → shiftUp v u ≡ u
shiftUpTrivial v (VAR x) i with x <? v
... | yes z = refl
... | no z = ⊥-elim (i x (sucLeInj (≰⇒> z)) (here refl))
shiftUpTrivial v NAT i = refl
shiftUpTrivial v QNAT i = refl
shiftUpTrivial v (LT u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (QLT u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (NUM x) i = refl
shiftUpTrivial v (PI u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (LAMBDA u) i
  rewrite shiftUpTrivial (suc v) u (impLeNotLower _ _ i) = refl
shiftUpTrivial v (APPLY u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (SUM u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (PAIR u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (SPREAD u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl
shiftUpTrivial v (SET u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (UNION u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (INL u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (INR u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (DECIDE u u₁ u₂) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite lowerVarsApp (fvars u₁) (fvars u₂)
  rewrite shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp1 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i)))
  rewrite shiftUpTrivial (suc v) u₂ (impLeNotLower _ _ (impLeNotApp2 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i))) = refl
shiftUpTrivial v (EQ u u₁ u₂) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
  rewrite shiftUpTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
shiftUpTrivial v AX i = refl
shiftUpTrivial v FREE i = refl
shiftUpTrivial v (CS x) i = refl
shiftUpTrivial v (TSQUASH u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (FFDEFS u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (UNIV x) i = refl
shiftUpTrivial v (LOWER u) i
  rewrite shiftUpTrivial v u i = refl

subNotIn : (t u : Term) → # u → sub t u ≡ u
subNotIn t u d rewrite subvNotIn 0 (shiftUp 0 t) u (d 0) = shiftDownTrivial 0 u (λ w c → d w)
\end{code}
