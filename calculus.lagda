\begin{code}
{-# OPTIONS --rewriting #-}

module calculus where

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
open import Data.Nat using (ℕ ; _≟_ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _⊔_)
open import Data.Nat.Properties
open import Data.Bool.Properties using ()
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Axiom.UniquenessOfIdentityProofs

open import util
\end{code}


\begin{code}
-- the Name of a choice operator is taken as being a ℕ here
Name : Set
Name = ℕ


freshNameAux : (l : List Name) → Σ Name (λ n → (x : Name) → x ∈ l → x < n)
freshNameAux [] = (0 , λ x i → ⊥-elim (¬∈[] i))
freshNameAux (n ∷ l) =
  let (m , c) = freshNameAux l in
  let z : suc (n ⊔ m) ≡ suc n ⊔ suc m
      z = refl in
  (suc (n ⊔ m) , λ { x (here p) → <-transˡ (subst (λ x → x < suc n) (sym p) (n<1+n n)) (≤⊔l (suc n) (suc m)) ;
                     x (there p) → let c1 = c x p in <-trans c1 (<-transˡ (n<1+n _) (≤⊔r (suc n) (suc m)))} )


freshName : (l : List Name) → Σ Name (λ n → ¬ (n ∈ l))
freshName l = let (m , c) = freshNameAux l in (m , λ x → let z = c _ x in n≮n _ z)


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
  FIX : Term → Term
  LET : Term → Term → Term
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
  -- Choices
  FREE : Term
  CS : Name → Term
  CHOOSE : Term → Term → Term
  IFC0 : Term → Term → Term → Term
  -- Time squashing
  TSQUASH : Term → Term
  -- Dummy
  DUM : Term → Term
  -- Free from definitions
  FFDEFS : Term → Term → Term
  -- Universes
  UNIV : ℕ → Term
  LIFT : Term -> Term
  --
  LOWER : Term -> Term
  SHRINK : Term -> Term


value? : Term → Bool
value? (VAR _) = false
value? NAT = true
value? QNAT = true
value? (LT _ _) = true
value? (QLT _ _) = true
value? (NUM _) = true
value? (PI _ _) = true
value? (LAMBDA _) = true
value? (APPLY _ _) = false -- Not a value
value? (FIX _) = false -- Not a value
value? (LET _ _) = false -- Not a value
value? (SUM _ _) = true
value? (PAIR _ _) = true
value? (SPREAD _ _) = false -- Not a value
value? (SET _ _) = true
value? (UNION _ _) = true
value? (INL _) = true
value? (INR _) = true
value? (DECIDE _ _ _) = false -- Not a value
value? (EQ _ _ _) = true
value? AX = true
value? FREE = true
value? (CS _) = true
value? (CHOOSE _ _) = false -- Not a value
value? (IFC0 _ _ _) = false -- Not a value
value? (TSQUASH _) = true
value? (DUM _) = true
value? (FFDEFS _ _) = true
value? (UNIV _) = true
value? (LIFT _) = true
value? (LOWER _) = true
value? (SHRINK _) = true


Bool→Set : Bool → Set
Bool→Set true = ⊤
Bool→Set false = ⊥


isValue : Term → Set
isValue t = Bool→Set (value? t)


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
fvars (FIX t)          = fvars t
fvars (LET t t₁)       = fvars t ++ lowerVars (fvars t₁)
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
fvars (CHOOSE a b)     = fvars a ++ fvars b
fvars (IFC0 a b c)     = fvars a ++ fvars b ++ fvars c
fvars (TSQUASH t)      = fvars t
fvars (DUM t)          = fvars t
fvars (FFDEFS t t₁)    = fvars t ++ fvars t₁
fvars (UNIV x)         = []
fvars (LIFT t)         = fvars t
fvars (LOWER t)        = fvars t
fvars (SHRINK t)        = fvars t


_#_ : (v : Var) (t : Term) → Set
v # t = ¬ (v ∈ fvars t)


-- closed expression
#_ : (t : Term) → Set₀
# t = fvars t ≡ []
--# t = ((fvars t) _≟_ []) ≡ true
--# t = (fvars t) ⊆? [] ≡ true


#eq : {a : Term} → (p q : # a) → q ≡ p
#eq {a} p q = Decidable⇒UIP.≡-irrelevant (Data.List.Properties.≡-dec Data.Nat.Properties._≟_) q p


_⊆?_ : (l k : List Var) → Bool
[] ⊆? k = true
(v ∷ l) ⊆? k with (v ∈? k)
... | yes _ = l ⊆? k
... | no _ = false


#[_]_ : (l : List Var) (t : Term) → Set
#[ l ] t = (fvars t) ⊆? l ≡ true


#[]eq : {l : List Var} {a : Term} → (p q : #[ l ] a) → q ≡ p
#[]eq {a} p q = Decidable⇒UIP.≡-irrelevant Data.Bool.Properties._≟_ q p


record CTerm : Set where
  constructor ct
  field
    cTerm  : Term
    closed : # cTerm


record CTerm0 : Set where
  constructor ct0
  field
    cTerm  : Term
    closed : #[ [ 0 ] ] cTerm



record ToTerm (A : Set) : Set where
  field
    ⌜_⌝ : A -> Term

open ToTerm {{...}} public


instance
  CTermToTerm : ToTerm CTerm
  ⌜_⌝ {{CTermToTerm}} t = CTerm.cTerm t

instance
  CTerm0ToTerm : ToTerm CTerm0
  ⌜_⌝ {{CTerm0ToTerm}} t = CTerm0.cTerm t


CTerm→CTerm0 : CTerm → CTerm0
CTerm→CTerm0 (ct t c) = ct0 t c'
  where
    c' : #[ [ 0 ] ] t
    c' rewrite c = refl


record fromCTerm (A : Set) : Set where
  field
    ⌞_⌟ : CTerm → A

open fromCTerm {{...}} public


instance
  CTermToCTerm0 : fromCTerm CTerm0
  ⌞_⌟ {{CTermToCTerm0}} t = CTerm→CTerm0 t


CTerm≡ : {a b : CTerm} → ⌜ a ⌝ ≡ ⌜ b ⌝ → a ≡ b
CTerm≡ {ct a ca} {ct .a cb} refl rewrite #eq {a} ca cb = refl


CTerm0≡ : {a b : CTerm0} → ⌜ a ⌝ ≡ ⌜ b ⌝ → a ≡ b
CTerm0≡ {ct0 a ca} {ct0 .a cb} refl rewrite #[]eq {[ 0 ]} {a} ca cb = refl


≡CTerm : {a b : CTerm} → a ≡ b → ⌜ a ⌝ ≡ ⌜ b ⌝
≡CTerm {ct a ca} {ct .a .ca} refl = refl


sucIf≤ : (c x : ℕ) → ℕ
sucIf≤ c x with x <? c
... | yes _ = x
... | no _ = suc x


predIf≤ : (c x : ℕ) → ℕ
predIf≤ c 0 = 0
predIf≤ c (suc x) with suc x ≤? c
... | yes _ = suc x
... | no _ = x


shiftUp : ℕ → Term → Term
shiftUp c (VAR x) = VAR (sucIf≤ c x)
shiftUp c NAT = NAT
shiftUp c QNAT = QNAT
shiftUp c (LT t t₁) = LT (shiftUp c t) (shiftUp c t₁)
shiftUp c (QLT t t₁) = QLT (shiftUp c t) (shiftUp c t₁)
shiftUp c (NUM x) = NUM x
shiftUp c (PI t t₁) = PI (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (LAMBDA t) = LAMBDA (shiftUp (suc c) t)
shiftUp c (APPLY t t₁) = APPLY (shiftUp c t) (shiftUp c t₁)
shiftUp c (FIX t) = FIX (shiftUp c t)
shiftUp c (LET t t₁) = LET (shiftUp c t) (shiftUp (suc c) t₁)
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
shiftUp c (CHOOSE a b) = CHOOSE (shiftUp c a) (shiftUp c b)
shiftUp c (IFC0 a t₁ t₂) = IFC0 (shiftUp c a) (shiftUp c t₁) (shiftUp c t₂)
shiftUp c (TSQUASH t) = TSQUASH (shiftUp c t)
shiftUp c (DUM t) = DUM (shiftUp c t)
shiftUp c (FFDEFS t t₁) = FFDEFS (shiftUp c t) (shiftUp c t₁)
shiftUp c (UNIV x) = UNIV x
shiftUp c (LIFT t) = LIFT (shiftUp c t)
shiftUp c (LOWER t) = LOWER (shiftUp c t)
shiftUp c (SHRINK t) = SHRINK (shiftUp c t)

shiftDown : ℕ → Term → Term
shiftDown c (VAR x) = VAR (predIf≤ c x)
shiftDown c NAT = NAT
shiftDown c QNAT = QNAT
shiftDown c (LT t t₁) = LT (shiftDown c t) (shiftDown c t₁)
shiftDown c (QLT t t₁) = QLT (shiftDown c t) (shiftDown c t₁)
shiftDown c (NUM x) = NUM x
shiftDown c (PI t t₁) = PI (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (LAMBDA t) = LAMBDA (shiftDown (suc c) t)
shiftDown c (APPLY t t₁) = APPLY (shiftDown c t) (shiftDown c t₁)
shiftDown c (FIX t) = FIX (shiftDown c t)
shiftDown c (LET t t₁) = LET (shiftDown c t) (shiftDown (suc c) t₁)
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
shiftDown c (CHOOSE a b) = CHOOSE (shiftDown c a) (shiftDown c b)
shiftDown c (IFC0 a t₁ t₂) = IFC0 (shiftDown c a) (shiftDown c t₁) (shiftDown c t₂)
shiftDown c (TSQUASH t) = TSQUASH (shiftDown c t)
shiftDown c (DUM t) = DUM (shiftDown c t)
shiftDown c (FFDEFS t t₁) = FFDEFS (shiftDown c t) (shiftDown c t₁)
shiftDown c (UNIV x) = UNIV x
shiftDown c (LIFT t) = LIFT (shiftDown c t)
shiftDown c (LOWER t) = LOWER (shiftDown c t)
shiftDown c (SHRINK t) = SHRINK (shiftDown c t)

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
subv v t (FIX u) = FIX (subv v t u)
subv v t (LET u u₁) = LET (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
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
subv v t (CHOOSE a b) = CHOOSE (subv v t a) (subv v t b)
subv v t (IFC0 a t₁ t₂) = IFC0 (subv v t a) (subv v t t₁) (subv v t t₂)
subv v t (TSQUASH u) = TSQUASH (subv v t u)
subv v t (DUM u) = DUM (subv v t u)
subv v t (FFDEFS u u₁) = FFDEFS (subv v t u) (subv v t u₁)
subv v t (UNIV x) = UNIV x
subv v t (LIFT u) = LIFT (subv v t u)
subv v t (LOWER u) = LOWER (subv v t u)
subv v t (SHRINK u) = SHRINK (subv v t u)

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
        | subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (QLT u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (NUM x) n = refl
subvNotIn v t (PI u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (LAMBDA u) n
  rewrite subvNotIn (suc v) (shiftUp 0 t) u (λ j → ⊥-elim (n (inLowerVars _ _ j))) = refl
subvNotIn v t (APPLY u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (FIX u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (LET u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (SUM u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (PAIR u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (SPREAD u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ (inLowerVars _ _ j)))) = refl
subvNotIn v t (SET u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
subvNotIn v t (UNION u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (INL u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (INR u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (DECIDE u u₁ u₂) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim
            (notInAppVars1 {v} {lowerVars (fvars u₁)} {_}
               (notInAppVars2 {v} {fvars u} {_} n)
               (inLowerVars _ _ j)))
        | subvNotIn (suc v) (shiftUp 0 t) u₂ (λ j → ⊥-elim
            (notInAppVars2 {v} {lowerVars (fvars u₁)} {_}
               (notInAppVars2 {v} {fvars u} {_} n)
               (inLowerVars _ _ j))) = refl
subvNotIn v t (EQ u u₁ u₂) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
        | subvNotIn v t u₂ (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)) = refl
subvNotIn v t AX n = refl
subvNotIn v t FREE n = refl
subvNotIn v t (CS x) n = refl
subvNotIn v t (CHOOSE u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (IFC0 u u₁ u₂) n
  rewrite subvNotIn v t u (notInAppVars1 n)
        | subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
        | subvNotIn v t u₂ (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)) = refl
subvNotIn v t (TSQUASH u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (DUM u) n
  rewrite subvNotIn v t u n = refl
subvNotIn v t (FFDEFS u u₁) n
  rewrite subvNotIn v t u (notInAppVars1 n)
  rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
subvNotIn v t (UNIV x) n = refl
subvNotIn v t (LIFT u) n rewrite subvNotIn v t u n = refl
subvNotIn v t (LOWER u) n rewrite subvNotIn v t u n = refl
subvNotIn v t (SHRINK u) n rewrite subvNotIn v t u n = refl

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
shiftDownTrivial v (VAR (suc x)) i with suc x ≤? v
... | yes z = refl
... | no z = ⊥-elim (i (suc x) (<⇒≤ (≰⇒> z)) (here refl)) --(i (suc x) (sucLeInj (≰⇒> z)) (here refl))
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
shiftDownTrivial v (FIX u) i
  rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (LET u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
  rewrite shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
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
        | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
        | shiftDownTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
shiftDownTrivial v AX i = refl
shiftDownTrivial v FREE i = refl
shiftDownTrivial v (CS x) i = refl
shiftDownTrivial v (CHOOSE u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (IFC0 u u₁ u₂) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
        | shiftDownTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
shiftDownTrivial v (TSQUASH u) i
  rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (DUM u) i
  rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (FFDEFS u u₁) i
  rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftDownTrivial v (UNIV x) i = refl
shiftDownTrivial v (LIFT u) i rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (LOWER u) i rewrite shiftDownTrivial v u i = refl
shiftDownTrivial v (SHRINK u) i rewrite shiftDownTrivial v u i = refl

shiftUpTrivial : (v : Var) (u : Term) → ((w : Var) → v ≤ w → w # u) → shiftUp v u ≡ u
shiftUpTrivial v (VAR x) i with x <? v
... | yes z = refl
... | no z = ⊥-elim (i x (sucLeInj (≰⇒> z)) (here refl))
shiftUpTrivial v NAT i = refl
shiftUpTrivial v QNAT i = refl
shiftUpTrivial v (LT u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (QLT u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (NUM x) i = refl
shiftUpTrivial v (PI u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (LAMBDA u) i
  rewrite shiftUpTrivial (suc v) u (impLeNotLower _ _ i) = refl
shiftUpTrivial v (APPLY u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (FIX u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (LET u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (SUM u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (PAIR u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (SPREAD u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl
shiftUpTrivial v (SET u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
shiftUpTrivial v (UNION u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (INL u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (INR u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (DECIDE u u₁ u₂) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | lowerVarsApp (fvars u₁) (fvars u₂)
        | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp1 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i)))
        | shiftUpTrivial (suc v) u₂ (impLeNotLower _ _ (impLeNotApp2 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i))) = refl
shiftUpTrivial v (EQ u u₁ u₂) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
        | shiftUpTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
shiftUpTrivial v AX i = refl
shiftUpTrivial v FREE i = refl
shiftUpTrivial v (CS x) i = refl
shiftUpTrivial v (CHOOSE u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (IFC0 u u₁ u₂) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
        | shiftUpTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
shiftUpTrivial v (TSQUASH u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (DUM u) i
  rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (FFDEFS u u₁) i
  rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
        | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
shiftUpTrivial v (UNIV x) i = refl
shiftUpTrivial v (LIFT u) i rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (LOWER u) i rewrite shiftUpTrivial v u i = refl
shiftUpTrivial v (SHRINK u) i rewrite shiftUpTrivial v u i = refl

#→¬∈ : {t : Term} → # t → (v : Var) → v # t
#→¬∈ {t} c v i rewrite c = x i
  where
    x : ¬ v ∈ []
    x ()

subNotIn : (t u : Term) → # u → sub t u ≡ u
subNotIn t u d rewrite subvNotIn 0 (shiftUp 0 t) u (#→¬∈ {u} d 0) = shiftDownTrivial 0 u (λ w c → #→¬∈ {u} d w)

shiftDownUp : (t : Term) (n : ℕ) → shiftDown n (shiftUp n t) ≡ t
shiftDownUp (VAR x) n with x <? n
shiftDownUp (VAR 0) n | yes p = refl
shiftDownUp (VAR (suc x)) n | yes p with suc x ≤? n
...                                    | yes q = refl
...                                    | no q = ⊥-elim (q (≤-trans (n≤1+n _) p))
shiftDownUp (VAR x) n | no p with suc x ≤? n
...                             | yes q = ⊥-elim (p q)
...                             | no q = refl
shiftDownUp NAT n = refl
shiftDownUp QNAT n = refl
shiftDownUp (LT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
shiftDownUp (QLT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
shiftDownUp (NUM x) n = refl
shiftDownUp (PI t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
shiftDownUp (LAMBDA t) n rewrite shiftDownUp t (suc n) = refl
shiftDownUp (APPLY t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
shiftDownUp (FIX t) n rewrite shiftDownUp t n = refl
shiftDownUp (LET t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
shiftDownUp (SUM t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
shiftDownUp (PAIR t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
shiftDownUp (SPREAD t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc (suc n)) = refl
shiftDownUp (SET t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
shiftDownUp (UNION t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
shiftDownUp (INL t) n rewrite shiftDownUp t n = refl
shiftDownUp (INR t) n rewrite shiftDownUp t n = refl
shiftDownUp (DECIDE t t₁ t₂) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) | shiftDownUp t₂ (suc n) = refl
shiftDownUp (EQ t t₁ t₂) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n = refl
shiftDownUp AX n = refl
shiftDownUp FREE n = refl
shiftDownUp (CS x) n = refl
shiftDownUp (CHOOSE t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
shiftDownUp (IFC0 t t₁ t₂) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n = refl
shiftDownUp (TSQUASH t) n rewrite shiftDownUp t n = refl
shiftDownUp (DUM t) n rewrite shiftDownUp t n = refl
shiftDownUp (FFDEFS t t₁) n rewrite shiftDownUp t n rewrite shiftDownUp t₁ n = refl
shiftDownUp (UNIV x) n = refl
shiftDownUp (LIFT t) n rewrite shiftDownUp t n = refl
shiftDownUp (LOWER t) n rewrite shiftDownUp t n = refl
shiftDownUp (SHRINK t) n rewrite shiftDownUp t n = refl


is-NUM : (t : Term) → (Σ ℕ (λ n → t ≡ NUM n)) ⊎ ((n : ℕ) → ¬ t ≡ NUM n)
is-NUM (VAR x) = inj₂ (λ { n () })
is-NUM NAT = inj₂ (λ { n () })
is-NUM QNAT = inj₂ (λ { n () })
is-NUM (LT t t₁) = inj₂ (λ { n () })
is-NUM (QLT t t₁) = inj₂ (λ { n () })
is-NUM (NUM x) = inj₁ ( x , refl)
is-NUM (PI t t₁) = inj₂ (λ { n () })
is-NUM (LAMBDA t) = inj₂ (λ { n () })
is-NUM (APPLY t t₁) = inj₂ (λ { n () })
is-NUM (FIX t) = inj₂ (λ { n () })
is-NUM (LET t t₁) = inj₂ (λ { n () })
is-NUM (SUM t t₁) = inj₂ (λ { n () })
is-NUM (PAIR t t₁) = inj₂ (λ { n () })
is-NUM (SPREAD t t₁) = inj₂ (λ { n () })
is-NUM (SET t t₁) = inj₂ (λ { n () })
is-NUM (UNION t t₁) = inj₂ (λ { n () })
is-NUM (INL t) = inj₂ (λ { n () })
is-NUM (INR t) = inj₂ (λ { n () })
is-NUM (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-NUM (EQ t t₁ t₂) = inj₂ (λ { n () })
is-NUM AX = inj₂ (λ { n () })
is-NUM FREE = inj₂ (λ { n () })
is-NUM (CS x) = inj₂ (λ { n () })
is-NUM (CHOOSE t t₁) = inj₂ (λ { n () })
is-NUM (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-NUM (TSQUASH t) = inj₂ (λ { n () })
is-NUM (DUM t) = inj₂ (λ { n () })
is-NUM (FFDEFS t t₁) = inj₂ (λ { n () })
is-NUM (UNIV x) = inj₂ (λ { n () })
is-NUM (LIFT t) = inj₂ (λ { n () })
is-NUM (LOWER t) = inj₂ (λ { n () })
is-NUM (SHRINK t) = inj₂ (λ { n () })


is-LAM : (t : Term) → (Σ Term (λ u → t ≡ LAMBDA u)) ⊎ ((u : Term) → ¬ t ≡ LAMBDA u)
is-LAM (VAR x) = inj₂ (λ { n () })
is-LAM NAT = inj₂ (λ { n () })
is-LAM QNAT = inj₂ (λ { n () })
is-LAM (LT t t₁) = inj₂ (λ { n () })
is-LAM (QLT t t₁) = inj₂ (λ { n () })
is-LAM (NUM x) = inj₂ (λ { n () })
is-LAM (PI t t₁) = inj₂ (λ { n () })
is-LAM (LAMBDA t) = inj₁ (t , refl)
is-LAM (APPLY t t₁) = inj₂ (λ { n () })
is-LAM (FIX t) = inj₂ (λ { n () })
is-LAM (LET t t₁) = inj₂ (λ { n () })
is-LAM (SUM t t₁) = inj₂ (λ { n () })
is-LAM (PAIR t t₁) = inj₂ (λ { n () })
is-LAM (SPREAD t t₁) = inj₂ (λ { n () })
is-LAM (SET t t₁) = inj₂ (λ { n () })
is-LAM (UNION t t₁) = inj₂ (λ { n () })
is-LAM (INL t) = inj₂ (λ { n () })
is-LAM (INR t) = inj₂ (λ { n () })
is-LAM (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-LAM (EQ t t₁ t₂) = inj₂ (λ { n () })
is-LAM AX = inj₂ (λ { n () })
is-LAM FREE = inj₂ (λ { n () })
is-LAM (CS x) = inj₂ (λ { n () })
is-LAM (CHOOSE t t₁) = inj₂ (λ { n () })
is-LAM (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-LAM (TSQUASH t) = inj₂ (λ { n () })
is-LAM (DUM t) = inj₂ (λ { n () })
is-LAM (FFDEFS t t₁) = inj₂ (λ { n () })
is-LAM (UNIV x) = inj₂ (λ { n () })
is-LAM (LIFT t) = inj₂ (λ { n () })
is-LAM (LOWER t) = inj₂ (λ { n () })
is-LAM (SHRINK t) = inj₂ (λ { n () })


is-CS : (t : Term) → (Σ Name (λ n → t ≡ CS n)) ⊎ ((n : Name) → ¬ t ≡ CS n)
is-CS (VAR x) = inj₂ (λ { n () })
is-CS NAT = inj₂ (λ { n () })
is-CS QNAT = inj₂ (λ { n () })
is-CS (LT t t₁) = inj₂ (λ { n () })
is-CS (QLT t t₁) = inj₂ (λ { n () })
is-CS (NUM x) = inj₂ (λ { n () })
is-CS (PI t t₁) = inj₂ (λ { n () })
is-CS (LAMBDA t) = inj₂ (λ { n () })
is-CS (APPLY t t₁) = inj₂ (λ { n () })
is-CS (FIX t) = inj₂ (λ { n () })
is-CS (LET t t₁) = inj₂ (λ { n () })
is-CS (SUM t t₁) = inj₂ (λ { n () })
is-CS (PAIR t t₁) = inj₂ (λ { n () })
is-CS (SPREAD t t₁) = inj₂ (λ { n () })
is-CS (SET t t₁) = inj₂ (λ { n () })
is-CS (UNION t t₁) = inj₂ (λ { n () })
is-CS (INL t) = inj₂ (λ { n () })
is-CS (INR t) = inj₂ (λ { n () })
is-CS (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-CS (EQ t t₁ t₂) = inj₂ (λ { n () })
is-CS AX = inj₂ (λ { n () })
is-CS FREE = inj₂ (λ { n () })
is-CS (CS x) = inj₁ (x , refl)
is-CS (CHOOSE t t₁) = inj₂ (λ { n () })
is-CS (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-CS (TSQUASH t) = inj₂ (λ { n () })
is-CS (DUM t) = inj₂ (λ { n () })
is-CS (FFDEFS t t₁) = inj₂ (λ { n () })
is-CS (UNIV x) = inj₂ (λ { n () })
is-CS (LIFT t) = inj₂ (λ { n () })
is-CS (LOWER t) = inj₂ (λ { n () })
is-CS (SHRINK t) = inj₂ (λ { n () })


is-PAIR : (t : Term) → (Σ Term (λ a → Σ Term (λ b → t ≡ PAIR a b))) ⊎ ((a b : Term) → ¬ t ≡ PAIR a b)
is-PAIR (VAR x) = inj₂ (λ { n m () })
is-PAIR NAT = inj₂ (λ { n m () })
is-PAIR QNAT = inj₂ (λ { n m () })
is-PAIR (LT t t₁) = inj₂ (λ { n m () })
is-PAIR (QLT t t₁) = inj₂ (λ { n m () })
is-PAIR (NUM x) = inj₂ (λ { n m () })
is-PAIR (PI t t₁) = inj₂ (λ { n m () })
is-PAIR (LAMBDA t) = inj₂ (λ { n m () })
is-PAIR (APPLY t t₁) = inj₂ (λ { n m () })
is-PAIR (FIX t) = inj₂ (λ { n m () })
is-PAIR (LET t t₁) = inj₂ (λ { n m () })
is-PAIR (SUM t t₁) = inj₂ (λ { n m () })
is-PAIR (PAIR t t₁) = inj₁ (t , t₁ , refl)
is-PAIR (SPREAD t t₁) = inj₂ (λ { n m () })
is-PAIR (SET t t₁) = inj₂ (λ { n m () })
is-PAIR (UNION t t₁) = inj₂ (λ { n m () })
is-PAIR (INL t) = inj₂ (λ { n m () })
is-PAIR (INR t) = inj₂ (λ { n m () })
is-PAIR (DECIDE t t₁ t₂) = inj₂ (λ { n m () })
is-PAIR (EQ t t₁ t₂) = inj₂ (λ { n m () })
is-PAIR AX = inj₂ (λ { n m () })
is-PAIR FREE = inj₂ (λ { n m () })
is-PAIR (CS x) = inj₂ (λ { n m () })
is-PAIR (CHOOSE t t₁) = inj₂ (λ { n m () })
is-PAIR (IFC0 t t₁ t₂) = inj₂ (λ { n m () })
is-PAIR (TSQUASH t) = inj₂ (λ { n m () })
is-PAIR (DUM t) = inj₂ (λ { n m () })
is-PAIR (FFDEFS t t₁) = inj₂ (λ { n m () })
is-PAIR (UNIV x) = inj₂ (λ { n m () })
is-PAIR (LIFT t) = inj₂ (λ { n m () })
is-PAIR (LOWER t) = inj₂ (λ { n m () })
is-PAIR (SHRINK t) = inj₂ (λ { n m () })


is-INL : (t : Term) → (Σ Term (λ u → t ≡ INL u)) ⊎ ((u : Term) → ¬ t ≡ INL u)
is-INL (VAR x) = inj₂ (λ { n () })
is-INL NAT = inj₂ (λ { n () })
is-INL QNAT = inj₂ (λ { n () })
is-INL (LT t t₁) = inj₂ (λ { n () })
is-INL (QLT t t₁) = inj₂ (λ { n () })
is-INL (NUM x) = inj₂ (λ { n () })
is-INL (PI t t₁) = inj₂ (λ { n () })
is-INL (LAMBDA t) = inj₂ (λ { n () })
is-INL (APPLY t t₁) = inj₂ (λ { n () })
is-INL (FIX t) = inj₂ (λ { n () })
is-INL (LET t t₁) = inj₂ (λ { n () })
is-INL (SUM t t₁) = inj₂ (λ { n () })
is-INL (PAIR t t₁) = inj₂ (λ { n () })
is-INL (SPREAD t t₁) = inj₂ (λ { n () })
is-INL (SET t t₁) = inj₂ (λ { n () })
is-INL (UNION t t₁) = inj₂ (λ { n () })
is-INL (INL t) = inj₁ (t , refl)
is-INL (INR t) = inj₂ (λ { n () })
is-INL (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-INL (EQ t t₁ t₂) = inj₂ (λ { n () })
is-INL AX = inj₂ (λ { n () })
is-INL FREE = inj₂ (λ { n () })
is-INL (CS x) = inj₂ (λ { n () })
is-INL (CHOOSE t t₁) = inj₂ (λ { n () })
is-INL (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-INL (TSQUASH t) = inj₂ (λ { n () })
is-INL (DUM t) = inj₂ (λ { n () })
is-INL (FFDEFS t t₁) = inj₂ (λ { n () })
is-INL (UNIV x) = inj₂ (λ { n () })
is-INL (LIFT t) = inj₂ (λ { n () })
is-INL (LOWER t) = inj₂ (λ { n () })
is-INL (SHRINK t) = inj₂ (λ { n () })


is-INR : (t : Term) → (Σ Term (λ u → t ≡ INR u)) ⊎ ((u : Term) → ¬ t ≡ INR u)
is-INR (VAR x) = inj₂ (λ { n () })
is-INR NAT = inj₂ (λ { n () })
is-INR QNAT = inj₂ (λ { n () })
is-INR (LT t t₁) = inj₂ (λ { n () })
is-INR (QLT t t₁) = inj₂ (λ { n () })
is-INR (NUM x) = inj₂ (λ { n () })
is-INR (PI t t₁) = inj₂ (λ { n () })
is-INR (LAMBDA t) = inj₂ (λ { n () })
is-INR (APPLY t t₁) = inj₂ (λ { n () })
is-INR (FIX t) = inj₂ (λ { n () })
is-INR (LET t t₁) = inj₂ (λ { n () })
is-INR (SUM t t₁) = inj₂ (λ { n () })
is-INR (PAIR t t₁) = inj₂ (λ { n () })
is-INR (SPREAD t t₁) = inj₂ (λ { n () })
is-INR (SET t t₁) = inj₂ (λ { n () })
is-INR (UNION t t₁) = inj₂ (λ { n () })
is-INR (INL t) = inj₂ (λ { n () })
is-INR (INR t) = inj₁ (t , refl)
is-INR (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-INR (EQ t t₁ t₂) = inj₂ (λ { n () })
is-INR AX = inj₂ (λ { n () })
is-INR FREE = inj₂ (λ { n () })
is-INR (CS x) = inj₂ (λ { n () })
is-INR (CHOOSE t t₁) = inj₂ (λ { n () })
is-INR (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-INR (TSQUASH t) = inj₂ (λ { n () })
is-INR (DUM t) = inj₂ (λ { n () })
is-INR (FFDEFS t t₁) = inj₂ (λ { n () })
is-INR (UNIV x) = inj₂ (λ { n () })
is-INR (LIFT t) = inj₂ (λ { n () })
is-INR (LOWER t) = inj₂ (λ { n () })
is-INR (SHRINK t) = inj₂ (λ { n () })




data ∼vals : Term → Term → Set where
  ∼vals-NAT     : ∼vals NAT NAT
  ∼vals-QNAT    : ∼vals QNAT QNAT
  ∼vals-LT      : {a b c d : Term} → ∼vals (LT a b) (LT c d)
  ∼vals-QLT     : {a b c d : Term} → ∼vals (QLT a b) (QLT c d)
  ∼vals-NUM     : {n : ℕ} → ∼vals (NUM n) (NUM n)
  ∼vals-PI      : {a b c d : Term} → ∼vals (PI a b) (PI c d)
  ∼vals-LAMBDA  : {a b : Term} → ∼vals (LAMBDA a) (LAMBDA b)
  ∼vals-SUM     : {a b c d : Term} → ∼vals (SUM a b) (SUM c d)
  ∼vals-PAIR    : {a b c d : Term} → ∼vals (PAIR a b) (PAIR c d)
  ∼vals-SET     : {a b c d : Term} → ∼vals (SET a b) (SET c d)
  ∼vals-UNION   : {a b c d : Term} → ∼vals (UNION a b) (UNION c d)
  ∼vals-INL     : {a b : Term} → ∼vals (INL a) (INL b)
  ∼vals-INR     : {a b : Term} → ∼vals (INR a) (INR b)
  ∼vals-EQ      : {a b c d e f : Term} → ∼vals (EQ a b c) (EQ d e f)
  ∼vals-AX      : ∼vals AX AX
  ∼vals-FREE    : ∼vals FREE FREE
  ∼vals-CS      : {n : Name} → ∼vals (CS n) (CS n)
  ∼vals-TSQUASH : {a b : Term} → ∼vals (TSQUASH a) (TSQUASH b)
  ∼vals-DUM     : {a b : Term} → ∼vals (DUM a) (DUM b)
  ∼vals-FFDEFS  : {a b c d : Term} → ∼vals (FFDEFS a b) (FFDEFS c d)
  ∼vals-UNIV    : {n : ℕ} → ∼vals (UNIV n) (UNIV n)
  ∼vals-LIFT    : {a b : Term} → ∼vals (LIFT a) (LIFT b)
  ∼vals-LOWER   : {a b : Term} → ∼vals (LOWER a) (LOWER b)
  ∼vals-SHRINK  : {a b : Term} → ∼vals (SHRINK a) (SHRINK b)


∼vals-sym : {a b : Term} → ∼vals a b → ∼vals b a
∼vals-sym {.NAT} {.NAT} ∼vals-NAT = ∼vals-NAT
∼vals-sym {.QNAT} {.QNAT} ∼vals-QNAT = ∼vals-QNAT
∼vals-sym {.(LT _ _)} {.(LT _ _)} ∼vals-LT = ∼vals-LT
∼vals-sym {.(QLT _ _)} {.(QLT _ _)} ∼vals-QLT = ∼vals-QLT
∼vals-sym {.(NUM _)} {.(NUM _)} ∼vals-NUM = ∼vals-NUM
∼vals-sym {.(PI _ _)} {.(PI _ _)} ∼vals-PI = ∼vals-PI
∼vals-sym {.(LAMBDA _)} {.(LAMBDA _)} ∼vals-LAMBDA = ∼vals-LAMBDA
∼vals-sym {.(SUM _ _)} {.(SUM _ _)} ∼vals-SUM = ∼vals-SUM
∼vals-sym {.(PAIR _ _)} {.(PAIR _ _)} ∼vals-PAIR = ∼vals-PAIR
∼vals-sym {.(SET _ _)} {.(SET _ _)} ∼vals-SET = ∼vals-SET
∼vals-sym {.(UNION _ _)} {.(UNION _ _)} ∼vals-UNION = ∼vals-UNION
∼vals-sym {.(INL _)} {.(INL _)} ∼vals-INL = ∼vals-INL
∼vals-sym {.(INR _)} {.(INR _)} ∼vals-INR = ∼vals-INR
∼vals-sym {.(EQ _ _ _)} {.(EQ _ _ _)} ∼vals-EQ = ∼vals-EQ
∼vals-sym {.AX} {.AX} ∼vals-AX = ∼vals-AX
∼vals-sym {.FREE} {.FREE} ∼vals-FREE = ∼vals-FREE
∼vals-sym {.(CS _)} {.(CS _)} ∼vals-CS = ∼vals-CS
∼vals-sym {.(TSQUASH _)} {.(TSQUASH _)} ∼vals-TSQUASH = ∼vals-TSQUASH
∼vals-sym {.(DUM _)} {.(DUM _)} ∼vals-DUM = ∼vals-DUM
∼vals-sym {.(FFDEFS _ _)} {.(FFDEFS _ _)} ∼vals-FFDEFS = ∼vals-FFDEFS
∼vals-sym {.(UNIV _)} {.(UNIV _)} ∼vals-UNIV = ∼vals-UNIV
∼vals-sym {.(LIFT _)} {.(LIFT _)} ∼vals-LIFT = ∼vals-LIFT
∼vals-sym {.(LOWER _)} {.(LOWER _)} ∼vals-LOWER = ∼vals-LOWER
∼vals-sym {.(SHRINK _)} {.(SHRINK _)} ∼vals-SHRINK = ∼vals-SHRINK


∼vals→isValue₁ : {a b : Term} → ∼vals a b → isValue a
∼vals→isValue₁ {NAT} {b} isv = tt
∼vals→isValue₁ {QNAT} {b} isv = tt
∼vals→isValue₁ {LT a a₁} {b} isv = tt
∼vals→isValue₁ {QLT a a₁} {b} isv = tt
∼vals→isValue₁ {NUM x} {b} isv = tt
∼vals→isValue₁ {PI a a₁} {b} isv = tt
∼vals→isValue₁ {LAMBDA a} {b} isv = tt
∼vals→isValue₁ {SUM a a₁} {b} isv = tt
∼vals→isValue₁ {PAIR a a₁} {b} isv = tt
∼vals→isValue₁ {SET a a₁} {b} isv = tt
∼vals→isValue₁ {UNION a a₁} {b} isv = tt
∼vals→isValue₁ {INL a} {b} isv = tt
∼vals→isValue₁ {INR a} {b} isv = tt
∼vals→isValue₁ {EQ a a₁ a₂} {b} isv = tt
∼vals→isValue₁ {AX} {b} isv = tt
∼vals→isValue₁ {FREE} {b} isv = tt
∼vals→isValue₁ {CS x} {b} isv = tt
∼vals→isValue₁ {TSQUASH a} {b} isv = tt
∼vals→isValue₁ {DUM a} {b} isv = tt
∼vals→isValue₁ {FFDEFS a a₁} {b} isv = tt
∼vals→isValue₁ {UNIV x} {b} isv = tt
∼vals→isValue₁ {LIFT a} {b} isv = tt
∼vals→isValue₁ {LOWER a} {b} isv = tt
∼vals→isValue₁ {SHRINK a} {b} isv = tt


∼vals→isValue₂ : {a b : Term} → ∼vals a b → isValue b
∼vals→isValue₂ {a} {VAR x} ()
∼vals→isValue₂ {a} {NAT} isv = tt
∼vals→isValue₂ {a} {QNAT} isv = tt
∼vals→isValue₂ {a} {LT b b₁} isv = tt
∼vals→isValue₂ {a} {QLT b b₁} isv = tt
∼vals→isValue₂ {a} {NUM x} isv = tt
∼vals→isValue₂ {a} {PI b b₁} isv = tt
∼vals→isValue₂ {a} {LAMBDA b} isv = tt
∼vals→isValue₂ {a} {APPLY b b₁} ()
∼vals→isValue₂ {a} {FIX b} ()
∼vals→isValue₂ {a} {LET b b₁} ()
∼vals→isValue₂ {a} {SUM b b₁} isv = tt
∼vals→isValue₂ {a} {PAIR b b₁} isv = tt
∼vals→isValue₂ {a} {SPREAD b b₁} ()
∼vals→isValue₂ {a} {SET b b₁} isv = tt
∼vals→isValue₂ {a} {UNION b b₁} isv = tt
∼vals→isValue₂ {a} {INL b} isv = tt
∼vals→isValue₂ {a} {INR b} isv = tt
∼vals→isValue₂ {a} {DECIDE b b₁ b₂} ()
∼vals→isValue₂ {a} {EQ b b₁ b₂} isv = tt
∼vals→isValue₂ {a} {AX} isv = tt
∼vals→isValue₂ {a} {FREE} isv = tt
∼vals→isValue₂ {a} {CS x} isv = tt
∼vals→isValue₂ {a} {TSQUASH b} isv = tt
∼vals→isValue₂ {a} {DUM b} isv = tt
∼vals→isValue₂ {a} {FFDEFS b b₁} isv = tt
∼vals→isValue₂ {a} {UNIV x} isv = tt
∼vals→isValue₂ {a} {LIFT b} isv = tt
∼vals→isValue₂ {a} {LOWER b} isv = tt
∼vals→isValue₂ {a} {SHRINK b} isv = tt


#∼vals : CTerm → CTerm → Set
#∼vals a b = ∼vals ⌜ a ⌝ ⌜ b ⌝


#isValue : CTerm -> Set
#isValue t = isValue ⌜ t ⌝
\end{code}
