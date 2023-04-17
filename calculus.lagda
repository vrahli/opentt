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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
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
open import name
\end{code}


\begin{code}
Var : Set
Var = ℕ


𝕊 : Set
𝕊 = ℕ → ℕ


data Term : Set where
  -- Variables
  VAR : Var → Term
  -- Numbers
  NAT : Term
  QNAT : Term
  TNAT : Term
  LT : Term → Term → Term
  QLT : Term → Term → Term
  NUM : ℕ → Term
  IFLT : Term → Term → Term → Term → Term
  IFEQ : Term → Term → Term → Term → Term
  SUC : Term → Term
  -- Products
  PI :  Term → Term → Term
  LAMBDA : Term → Term
  APPLY : Term → Term → Term
  FIX : Term → Term
  LET : Term → Term → Term
  -- W
  WT :  Term → Term → Term
  SUP : Term → Term → Term
--  DSUP : Term → Term → Term
  WREC : Term → Term → Term
  -- M
  MT :  Term → Term → Term
--  MSUP : Term → Term → Term -- Let's not use MSUP and DMSUP, but reuse SUP and DSUP instead
--  DMSUP : Term → Term → Term
  -- Sums
  SUM : Term → Term → Term
  PAIR : Term → Term → Term
  SPREAD : Term → Term → Term
  -- Sets --- they don't have constructors/destructors
  SET : Term → Term → Term
  -- Unions
  TUNION : Term → Term → Term
  -- Binary intersection --- they don't have constructors/destructors
  ISECT : Term → Term → Term
  -- Disjoint unions
  UNION : Term → Term → Term
  QTUNION : Term → Term → Term
  INL : Term → Term
  INR : Term → Term
  DECIDE : Term → Term → Term → Term
  -- Equality
  EQ : Term → Term → Term → Term
  EQB : Term → Term → Term → Term → Term
  AX : Term
  -- Choices
  FREE : Term
  CS : Name → Term
  NAME : Name → Term
  FRESH : Term → Term
  CHOOSE : Term → Term → Term
  LOAD : Term → Term
  -- Internal sequences
  MSEQ : 𝕊 → Term -- used for termination
  MAPP : 𝕊 → Term → Term
--  IFC0 : Term → Term → Term → Term
  -- Truncation
  TSQUASH : Term → Term -- closed under ∼C
  TTRUNC : Term → Term  -- closed under #⇓
  TCONST : Term → Term  -- satisfy #⇓→#⇓!
  SUBSING : Term → Term
  -- Dummy
  DUM : Term → Term
  -- Free from definitions
  FFDEFS : Term → Term → Term
  PURE : Term
  -- Terminating
  TERM : Term → Term
  ENC  : Term → Term
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
value? TNAT = true
value? (LT _ _) = true
value? (QLT _ _) = true
value? (NUM _) = true
value? (IFLT _ _ _ _) = false -- Not a value
value? (IFEQ _ _ _ _) = false -- Not a value
value? (SUC _) = false -- Not a value
value? (PI _ _) = true
value? (LAMBDA _) = true
value? (APPLY _ _) = false -- Not a value
value? (FIX _) = false -- Not a value
value? (LET _ _) = false -- Not a value
value? (WT _ _) = true
value? (SUP _ _) = true
--value? (DSUP _ _) = false -- Not a value
value? (WREC _ _) = false -- Not a value
value? (MT _ _) = true
--value? (MSUP _ _) = true
--value? (DMSUP _ _) = false -- Not a value
value? (SUM _ _) = true
value? (PAIR _ _) = true
value? (SPREAD _ _) = false -- Not a value
value? (SET _ _) = true
value? (ISECT _ _) = true
value? (TUNION _ _) = true
value? (UNION _ _) = true
value? (QTUNION _ _) = true
value? (INL _) = true
value? (INR _) = true
value? (DECIDE _ _ _) = false -- Not a value
value? (EQ _ _ _) = true
value? (EQB _ _ _ _) = true
value? AX = true
value? FREE = true
value? (MSEQ _) = true
value? (MAPP _ _) = false
value? (CS _) = true
value? (NAME _) = true
value? (FRESH _) = false
value? (LOAD _) = false
value? (CHOOSE _ _) = false -- Not a value
--value? (IFC0 _ _ _) = false -- Not a value
value? (TSQUASH _) = true
value? (TTRUNC _) = true
value? (TCONST _) = true
value? (SUBSING _) = true
value? (DUM _) = true
value? (FFDEFS _ _) = true
value? PURE = true
value? (TERM _) = true
value? (ENC _) = false
value? (UNIV _) = true
value? (LIFT _) = true
value? (LOWER _) = true
value? (SHRINK _) = true


Bool→Set : Bool → Set
Bool→Set true = ⊤
Bool→Set false = ⊥


isValue : Term → Set
isValue t = Bool→Set (value? t)


isValue⊎ : (t : Term) → isValue t ⊎ ¬ isValue t
isValue⊎ t with value? t
... | true = inj₁ tt
... | false = inj₂ λ x → x


{--
-- all variables
vars : Term → List Var
vars (VAR x) = [ x ]
vars NAT = []
vars QNAT = []
vars TNAT = []
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
vars (ISECT t t₁) = vars t ++ vars t₁
vars (UNION t t₁) = vars t ++ vars t₁
vars (INL t) = vars t
vars (INR t) = vars t
vars (DECIDE t x₁ t₁ x₂ t₂) = x₁ ∷ x₂ ∷ vars t ++ vars t₁ ++ vars t₂
vars (EQ t t₁ t₂) = vars t ++ vars t₁ ++ vars t₂
vars (EQB t t₁ t₂ t₃) = vars t ++ vars t₁ ++ vars t₂ ++ vars t₃
vars AX = []
vars FREE = []
vars (CS x) = []
vars (NAME x) = []
vars (TSQUASH t) = vars t
vars (TTRUNC t) = vars t
vars (TCONST t) = vars t
vars (SUBSING t) = vars t
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


diffName : Name → Pred Name 0ℓ
diffName x n with x ≟ n
... | yes p = ⊥
... | no p = ⊤


DecDiffName : (x : Name) → Decidable (diffName x)
DecDiffName x n with x ≟ n
... | yes p = false because ofⁿ (λ ())
... | no p = true because ofʸ tt


-- free variables
fvars : Term → List Var
fvars (VAR x)          = [ x ]
fvars NAT              = []
fvars QNAT             = []
fvars TNAT             = []
fvars (LT t t₁)        = fvars t ++ fvars t₁
fvars (QLT t t₁)       = fvars t ++ fvars t₁
fvars (NUM x)          = []
fvars (IFLT a b c d)   = fvars a ++ fvars b ++ fvars c ++ fvars d
fvars (IFEQ a b c d)   = fvars a ++ fvars b ++ fvars c ++ fvars d
fvars (SUC a)          = fvars a
fvars (PI t t₁)        = fvars t ++ lowerVars (fvars t₁)
fvars (LAMBDA t)       = lowerVars (fvars t)
fvars (APPLY t t₁)     = fvars t ++ fvars t₁
fvars (FIX t)          = fvars t
fvars (LET t t₁)       = fvars t ++ lowerVars (fvars t₁)
fvars (WT t t₁)        = fvars t ++ lowerVars (fvars t₁)
fvars (SUP t t₁)       = fvars t ++ fvars t₁
--fvars (DSUP t t₁)      = fvars t ++ lowerVars (lowerVars (fvars t₁))
fvars (WREC t t₁)      = fvars t ++ lowerVars (lowerVars (lowerVars (fvars t₁)))
fvars (MT t t₁)        = fvars t ++ lowerVars (fvars t₁)
--fvars (MSUP t t₁)      = fvars t ++ fvars t₁
--fvars (DMSUP t t₁)     = fvars t ++ lowerVars (lowerVars (fvars t₁))
fvars (SUM t t₁)       = fvars t ++ lowerVars (fvars t₁)
fvars (PAIR t t₁)      = fvars t ++ fvars t₁
fvars (SPREAD t t₁)    = fvars t ++ lowerVars (lowerVars (fvars t₁))
fvars (SET t t₁)       = fvars t ++ lowerVars (fvars t₁)
fvars (ISECT t t₁)     = fvars t ++ fvars t₁
fvars (TUNION t t₁)    = fvars t ++ lowerVars (fvars t₁)
fvars (UNION t t₁)     = fvars t ++ fvars t₁
fvars (QTUNION t t₁)   = fvars t ++ fvars t₁
fvars (INL t)          = fvars t
fvars (INR t)          = fvars t
fvars (DECIDE t t₁ t₂) = fvars t ++ lowerVars (fvars t₁) ++ lowerVars (fvars t₂)
fvars (EQ t t₁ t₂)     = fvars t ++ fvars t₁ ++ fvars t₂
fvars (EQB t t₁ t₂ t₃) = fvars t ++ fvars t₁ ++ fvars t₂ ++ fvars t₃
fvars AX               = []
fvars FREE             = []
fvars (MSEQ s)         = []
fvars (MAPP s t)       = fvars t
fvars (CS x)           = []
fvars (NAME x)         = []
fvars (FRESH t)        = fvars t
fvars (LOAD t)         = []
fvars (CHOOSE a b)     = fvars a ++ fvars b
--fvars (IFC0 a b c)     = fvars a ++ fvars b ++ fvars c
fvars (TSQUASH t)      = fvars t
fvars (TTRUNC t)       = fvars t
fvars (TCONST t)       = fvars t
fvars (SUBSING t)      = fvars t
fvars (DUM t)          = fvars t
fvars (FFDEFS t t₁)    = fvars t ++ fvars t₁
fvars PURE             = []
fvars (TERM t)         = fvars t
fvars (ENC t)          = [] --fvars t -- t is a CTerm
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
shiftUp c TNAT = TNAT
shiftUp c (LT t t₁) = LT (shiftUp c t) (shiftUp c t₁)
shiftUp c (QLT t t₁) = QLT (shiftUp c t) (shiftUp c t₁)
shiftUp c (NUM x) = NUM x
shiftUp c (IFLT t t₁ t₂ t₃) = IFLT (shiftUp c t) (shiftUp c t₁) (shiftUp c t₂) (shiftUp c t₃)
shiftUp c (IFEQ t t₁ t₂ t₃) = IFEQ (shiftUp c t) (shiftUp c t₁) (shiftUp c t₂) (shiftUp c t₃)
shiftUp c (SUC t) = SUC (shiftUp c t)
shiftUp c (PI t t₁) = PI (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (LAMBDA t) = LAMBDA (shiftUp (suc c) t)
shiftUp c (APPLY t t₁) = APPLY (shiftUp c t) (shiftUp c t₁)
shiftUp c (FIX t) = FIX (shiftUp c t)
shiftUp c (LET t t₁) = LET (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (WT t t₁) = WT (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (SUP t t₁) = SUP (shiftUp c t) (shiftUp c t₁)
--shiftUp c (DSUP t t₁) = DSUP (shiftUp c t) (shiftUp (suc (suc c)) t₁)
shiftUp c (WREC t t₁) = WREC (shiftUp c t) (shiftUp (suc (suc (suc c))) t₁)
shiftUp c (MT t t₁) = MT (shiftUp c t) (shiftUp (suc c) t₁)
--shiftUp c (MSUP t t₁) = MSUP (shiftUp c t) (shiftUp c t₁)
--shiftUp c (DMSUP t t₁) = DMSUP (shiftUp c t) (shiftUp (suc (suc c)) t₁)
shiftUp c (SUM t t₁) = SUM (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (PAIR t t₁) = PAIR (shiftUp c t) (shiftUp c t₁)
shiftUp c (SPREAD t t₁) = SPREAD (shiftUp c t) (shiftUp (suc (suc c)) t₁)
shiftUp c (SET t t₁) = SET (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (ISECT t t₁) = ISECT (shiftUp c t) (shiftUp c t₁)
shiftUp c (TUNION t t₁) = TUNION (shiftUp c t) (shiftUp (suc c) t₁)
shiftUp c (UNION t t₁) = UNION (shiftUp c t) (shiftUp c t₁)
shiftUp c (QTUNION t t₁) = QTUNION (shiftUp c t) (shiftUp c t₁)
shiftUp c (INL t) = INL (shiftUp c t)
shiftUp c (INR t) = INR (shiftUp c t)
shiftUp c (DECIDE t t₁ t₂) = DECIDE (shiftUp c t) (shiftUp (suc c) t₁) (shiftUp (suc c) t₂)
shiftUp c (EQ t t₁ t₂) = EQ (shiftUp c t) (shiftUp c t₁) (shiftUp c t₂)
shiftUp c (EQB t t₁ t₂ t₃) = EQB (shiftUp c t) (shiftUp c t₁) (shiftUp c t₂) (shiftUp c t₃)
shiftUp c AX = AX
shiftUp c FREE = FREE
shiftUp c (MSEQ x) = MSEQ x
shiftUp c (MAPP s t) = MAPP s (shiftUp c t)
shiftUp c (CS x) = CS x
shiftUp c (NAME x) = NAME x
shiftUp c (FRESH t) = FRESH (shiftUp c t)
shiftUp c (LOAD t) = LOAD t
shiftUp c (CHOOSE a b) = CHOOSE (shiftUp c a) (shiftUp c b)
--shiftUp c (IFC0 a t₁ t₂) = IFC0 (shiftUp c a) (shiftUp c t₁) (shiftUp c t₂)
shiftUp c (TSQUASH t) = TSQUASH (shiftUp c t)
shiftUp c (TTRUNC t) = TTRUNC (shiftUp c t)
shiftUp c (TCONST t) = TCONST (shiftUp c t)
shiftUp c (SUBSING t) = SUBSING (shiftUp c t)
shiftUp c (DUM t) = DUM (shiftUp c t)
shiftUp c (FFDEFS t t₁) = FFDEFS (shiftUp c t) (shiftUp c t₁)
shiftUp c PURE = PURE
shiftUp c (TERM t) = TERM (shiftUp c t)
shiftUp c (ENC t) = ENC t --(shiftUp c t)
shiftUp c (UNIV x) = UNIV x
shiftUp c (LIFT t) = LIFT (shiftUp c t)
shiftUp c (LOWER t) = LOWER (shiftUp c t)
shiftUp c (SHRINK t) = SHRINK (shiftUp c t)


shiftDown : ℕ → Term → Term
shiftDown c (VAR x) = VAR (predIf≤ c x)
shiftDown c NAT = NAT
shiftDown c QNAT = QNAT
shiftDown c TNAT = TNAT
shiftDown c (LT t t₁) = LT (shiftDown c t) (shiftDown c t₁)
shiftDown c (QLT t t₁) = QLT (shiftDown c t) (shiftDown c t₁)
shiftDown c (NUM x) = NUM x
shiftDown c (IFLT t t₁ t₂ t₃) = IFLT (shiftDown c t) (shiftDown c t₁) (shiftDown c t₂) (shiftDown c t₃)
shiftDown c (IFEQ t t₁ t₂ t₃) = IFEQ (shiftDown c t) (shiftDown c t₁) (shiftDown c t₂) (shiftDown c t₃)
shiftDown c (SUC t) = SUC (shiftDown c t)
shiftDown c (PI t t₁) = PI (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (LAMBDA t) = LAMBDA (shiftDown (suc c) t)
shiftDown c (APPLY t t₁) = APPLY (shiftDown c t) (shiftDown c t₁)
shiftDown c (FIX t) = FIX (shiftDown c t)
shiftDown c (LET t t₁) = LET (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (WT t t₁) = WT (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (SUP t t₁) = SUP (shiftDown c t) (shiftDown c t₁)
--shiftDown c (DSUP t t₁) = DSUP (shiftDown c t) (shiftDown (suc (suc c)) t₁)
shiftDown c (WREC t t₁) = WREC (shiftDown c t) (shiftDown (suc (suc (suc c))) t₁)
shiftDown c (MT t t₁) = MT (shiftDown c t) (shiftDown (suc c) t₁)
--shiftDown c (MSUP t t₁) = MSUP (shiftDown c t) (shiftDown c t₁)
--shiftDown c (DMSUP t t₁) = DMSUP (shiftDown c t) (shiftDown (suc (suc c)) t₁)
shiftDown c (SUM t t₁) = SUM (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (PAIR t t₁) = PAIR (shiftDown c t) (shiftDown c t₁)
shiftDown c (SPREAD t t₁) = SPREAD (shiftDown c t) (shiftDown (suc (suc c)) t₁)
shiftDown c (SET t t₁) = SET (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (ISECT t t₁) = ISECT (shiftDown c t) (shiftDown c t₁)
shiftDown c (TUNION t t₁) = TUNION (shiftDown c t) (shiftDown (suc c) t₁)
shiftDown c (UNION t t₁) = UNION (shiftDown c t) (shiftDown c t₁)
shiftDown c (QTUNION t t₁) = QTUNION (shiftDown c t) (shiftDown c t₁)
shiftDown c (INL t) = INL (shiftDown c t)
shiftDown c (INR t) = INR (shiftDown c t)
shiftDown c (DECIDE t t₁ t₂) = DECIDE (shiftDown c t) (shiftDown (suc c) t₁) (shiftDown (suc c) t₂)
shiftDown c (EQ t t₁ t₂) = EQ (shiftDown c t) (shiftDown c t₁) (shiftDown c t₂)
shiftDown c (EQB t t₁ t₂ t₃) = EQB (shiftDown c t) (shiftDown c t₁) (shiftDown c t₂) (shiftDown c t₃)
shiftDown c AX = AX
shiftDown c FREE = FREE
shiftDown c (MSEQ x) = MSEQ x
shiftDown c (MAPP s t) = MAPP s (shiftDown c t)
shiftDown c (CS x) = CS x
shiftDown c (NAME x) = NAME x
shiftDown c (FRESH a) = FRESH (shiftDown c a)
shiftDown c (LOAD a) = LOAD a
shiftDown c (CHOOSE a b) = CHOOSE (shiftDown c a) (shiftDown c b)
--shiftDown c (IFC0 a t₁ t₂) = IFC0 (shiftDown c a) (shiftDown c t₁) (shiftDown c t₂)
shiftDown c (TSQUASH t) = TSQUASH (shiftDown c t)
shiftDown c (TTRUNC t) = TTRUNC (shiftDown c t)
shiftDown c (TCONST t) = TCONST (shiftDown c t)
shiftDown c (SUBSING t) = SUBSING (shiftDown c t)
shiftDown c (DUM t) = DUM (shiftDown c t)
shiftDown c (FFDEFS t t₁) = FFDEFS (shiftDown c t) (shiftDown c t₁)
shiftDown c PURE = PURE
shiftDown c (TERM t) = TERM (shiftDown c t)
shiftDown c (ENC t) = ENC t --(shiftDown c t)
shiftDown c (UNIV x) = UNIV x
shiftDown c (LIFT t) = LIFT (shiftDown c t)
shiftDown c (LOWER t) = LOWER (shiftDown c t)
shiftDown c (SHRINK t) = SHRINK (shiftDown c t)


shiftNameUp : ℕ → Term → Term
shiftNameUp c (VAR x) = VAR x
shiftNameUp c NAT = NAT
shiftNameUp c QNAT = QNAT
shiftNameUp c TNAT = TNAT
shiftNameUp c (LT t t₁) = LT (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (QLT t t₁) = QLT (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (NUM x) = NUM x
shiftNameUp c (IFLT t t₁ t₂ t₃) = IFLT (shiftNameUp c t) (shiftNameUp c t₁) (shiftNameUp c t₂) (shiftNameUp c t₃)
shiftNameUp c (IFEQ t t₁ t₂ t₃) = IFEQ (shiftNameUp c t) (shiftNameUp c t₁) (shiftNameUp c t₂) (shiftNameUp c t₃)
shiftNameUp c (SUC t) = SUC (shiftNameUp c t)
shiftNameUp c (PI t t₁) = PI (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (LAMBDA t) = LAMBDA (shiftNameUp c t)
shiftNameUp c (APPLY t t₁) = APPLY (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (FIX t) = FIX (shiftNameUp c t)
shiftNameUp c (LET t t₁) = LET (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (WT t t₁) = WT (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (SUP t t₁) = SUP (shiftNameUp c t) (shiftNameUp c t₁)
--shiftNameUp c (DSUP t t₁) = DSUP (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (WREC t t₁) = WREC (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (MT t t₁) = MT (shiftNameUp c t) (shiftNameUp c t₁)
--shiftNameUp c (MSUP t t₁) = MSUP (shiftNameUp c t) (shiftNameUp c t₁)
--shiftNameUp c (DMSUP t t₁) = DMSUP (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (SUM t t₁) = SUM (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (PAIR t t₁) = PAIR (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (SPREAD t t₁) = SPREAD (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (SET t t₁) = SET (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (ISECT t t₁) = ISECT (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (TUNION t t₁) = TUNION (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (UNION t t₁) = UNION (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (QTUNION t t₁) = QTUNION (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c (INL t) = INL (shiftNameUp c t)
shiftNameUp c (INR t) = INR (shiftNameUp c t)
shiftNameUp c (DECIDE t t₁ t₂) = DECIDE (shiftNameUp c t) (shiftNameUp c t₁) (shiftNameUp c t₂)
shiftNameUp c (EQ t t₁ t₂) = EQ (shiftNameUp c t) (shiftNameUp c t₁) (shiftNameUp c t₂)
shiftNameUp c (EQB t t₁ t₂ t₃) = EQB (shiftNameUp c t) (shiftNameUp c t₁) (shiftNameUp c t₂) (shiftNameUp c t₃)
shiftNameUp c AX = AX
shiftNameUp c FREE = FREE
shiftNameUp c (MSEQ x) = MSEQ x
shiftNameUp c (MAPP s t) = MAPP s (shiftNameUp c t)
shiftNameUp c (CS x) = CS (sucIf≤ c x)
shiftNameUp c (NAME x) = NAME (sucIf≤ c x)
shiftNameUp c (FRESH t) = FRESH (shiftNameUp (suc c) t)
shiftNameUp c (LOAD t) = LOAD t
shiftNameUp c (CHOOSE a b) = CHOOSE (shiftNameUp c a) (shiftNameUp c b)
--shiftNameUp c (IFC0 a t₁ t₂) = IFC0 (shiftNameUp c a) (shiftNameUp c t₁) (shiftNameUp c t₂)
shiftNameUp c (TSQUASH t) = TSQUASH (shiftNameUp c t)
shiftNameUp c (TTRUNC t) = TTRUNC (shiftNameUp c t)
shiftNameUp c (TCONST t) = TCONST (shiftNameUp c t)
shiftNameUp c (SUBSING t) = SUBSING (shiftNameUp c t)
shiftNameUp c (DUM t) = DUM (shiftNameUp c t)
shiftNameUp c (FFDEFS t t₁) = FFDEFS (shiftNameUp c t) (shiftNameUp c t₁)
shiftNameUp c PURE = PURE
shiftNameUp c (TERM t) = TERM (shiftNameUp c t)
shiftNameUp c (ENC t) = ENC (shiftNameUp c t)
shiftNameUp c (UNIV x) = UNIV x
shiftNameUp c (LIFT t) = LIFT (shiftNameUp c t)
shiftNameUp c (LOWER t) = LOWER (shiftNameUp c t)
shiftNameUp c (SHRINK t) = SHRINK (shiftNameUp c t)


shiftNameDown : ℕ → Term → Term
shiftNameDown c (VAR x) = VAR x
shiftNameDown c NAT = NAT
shiftNameDown c QNAT = QNAT
shiftNameDown c TNAT = TNAT
shiftNameDown c (LT t t₁) = LT (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (QLT t t₁) = QLT (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (NUM x) = NUM x
shiftNameDown c (IFLT t t₁ t₂ t₃) = IFLT (shiftNameDown c t) (shiftNameDown c t₁) (shiftNameDown c t₂) (shiftNameDown c t₃)
shiftNameDown c (IFEQ t t₁ t₂ t₃) = IFEQ (shiftNameDown c t) (shiftNameDown c t₁) (shiftNameDown c t₂) (shiftNameDown c t₃)
shiftNameDown c (SUC t) = SUC (shiftNameDown c t)
shiftNameDown c (PI t t₁) = PI (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (LAMBDA t) = LAMBDA (shiftNameDown c t)
shiftNameDown c (APPLY t t₁) = APPLY (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (FIX t) = FIX (shiftNameDown c t)
shiftNameDown c (LET t t₁) = LET (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (WT t t₁) = WT (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (SUP t t₁) = SUP (shiftNameDown c t) (shiftNameDown c t₁)
--shiftNameDown c (DSUP t t₁) = DSUP (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (WREC t t₁) = WREC (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (MT t t₁) = MT (shiftNameDown c t) (shiftNameDown c t₁)
--shiftNameDown c (MSUP t t₁) = MSUP (shiftNameDown c t) (shiftNameDown c t₁)
--shiftNameDown c (DMSUP t t₁) = DMSUP (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (SUM t t₁) = SUM (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (PAIR t t₁) = PAIR (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (SPREAD t t₁) = SPREAD (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (SET t t₁) = SET (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (ISECT t t₁) = ISECT (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (TUNION t t₁) = TUNION (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (UNION t t₁) = UNION (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (QTUNION t t₁) = QTUNION (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c (INL t) = INL (shiftNameDown c t)
shiftNameDown c (INR t) = INR (shiftNameDown c t)
shiftNameDown c (DECIDE t t₁ t₂) = DECIDE (shiftNameDown c t) (shiftNameDown c t₁) (shiftNameDown c t₂)
shiftNameDown c (EQ t t₁ t₂) = EQ (shiftNameDown c t) (shiftNameDown c t₁) (shiftNameDown c t₂)
shiftNameDown c (EQB t t₁ t₂ t₃) = EQB (shiftNameDown c t) (shiftNameDown c t₁) (shiftNameDown c t₂) (shiftNameDown c t₃)
shiftNameDown c AX = AX
shiftNameDown c FREE = FREE
shiftNameDown c (MSEQ x) = MSEQ x
shiftNameDown c (MAPP s t) = MAPP s (shiftNameDown c t)
shiftNameDown c (CS x) = CS (predIf≤ c x)
shiftNameDown c (NAME x) = NAME (predIf≤ c x)
shiftNameDown c (FRESH a) = FRESH (shiftNameDown (suc c) a)
shiftNameDown c (LOAD a) = LOAD a
shiftNameDown c (CHOOSE a b) = CHOOSE (shiftNameDown c a) (shiftNameDown c b)
--shiftNameDown c (IFC0 a t₁ t₂) = IFC0 (shiftNameDown c a) (shiftNameDown c t₁) (shiftNameDown c t₂)
shiftNameDown c (TSQUASH t) = TSQUASH (shiftNameDown c t)
shiftNameDown c (TTRUNC t) = TTRUNC (shiftNameDown c t)
shiftNameDown c (TCONST t) = TCONST (shiftNameDown c t)
shiftNameDown c (SUBSING t) = SUBSING (shiftNameDown c t)
shiftNameDown c (DUM t) = DUM (shiftNameDown c t)
shiftNameDown c (FFDEFS t t₁) = FFDEFS (shiftNameDown c t) (shiftNameDown c t₁)
shiftNameDown c PURE = PURE
shiftNameDown c (TERM t) = TERM (shiftNameDown c t)
shiftNameDown c (ENC t) = ENC (shiftNameDown c t)
shiftNameDown c (UNIV x) = UNIV x
shiftNameDown c (LIFT t) = LIFT (shiftNameDown c t)
shiftNameDown c (LOWER t) = LOWER (shiftNameDown c t)
shiftNameDown c (SHRINK t) = SHRINK (shiftNameDown c t)


lowerNames : List Name → List Name
lowerNames [] = []
lowerNames (0 ∷ l) = lowerNames l
lowerNames (suc n ∷ l) = n ∷ lowerNames l


-- free names
names : Term → List Name
names (VAR x)          = []
names NAT              = []
names QNAT             = []
names TNAT             = []
names (LT t t₁)        = names t ++ names t₁
names (QLT t t₁)       = names t ++ names t₁
names (NUM x)          = []
names (IFLT a b c d)   = names a ++ names b ++ names c ++ names d
names (IFEQ a b c d)   = names a ++ names b ++ names c ++ names d
names (SUC a)          = names a
names (PI t t₁)        = names t ++ names t₁
names (LAMBDA t)       = names t
names (APPLY t t₁)     = names t ++ names t₁
names (FIX t)          = names t
names (LET t t₁)       = names t ++ names t₁
names (WT t t₁)        = names t ++ names t₁
names (SUP t t₁)       = names t ++ names t₁
--names (DSUP t t₁)      = names t ++ names t₁
names (WREC t t₁)      = names t ++ names t₁
names (MT t t₁)        = names t ++ names t₁
--names (MSUP t t₁)      = names t ++ names t₁
--names (DMSUP t t₁)     = names t ++ names t₁
names (SUM t t₁)       = names t ++ names t₁
names (PAIR t t₁)      = names t ++ names t₁
names (SPREAD t t₁)    = names t ++ names t₁
names (SET t t₁)       = names t ++ names t₁
names (ISECT t t₁)     = names t ++ names t₁
names (TUNION t t₁)    = names t ++ names t₁
names (UNION t t₁)     = names t ++ names t₁
names (QTUNION t t₁)   = names t ++ names t₁
names (INL t)          = names t
names (INR t)          = names t
names (DECIDE t t₁ t₂) = names t ++ names t₁ ++ names t₂
names (EQ t t₁ t₂)     = names t ++ names t₁ ++ names t₂
names (EQB t t₁ t₂ t₃) = names t ++ names t₁ ++ names t₂ ++ names t₃
names AX               = []
names FREE             = []
names (MSEQ x)         = []
names (MAPP s t)       = names t
names (CS x)           = [ x ]
names (NAME x)         = [ x ]
names (FRESH t)        = lowerNames (names t)
names (LOAD t)         = []
names (CHOOSE a b)     = names a ++ names b
--names (IFC0 a b c)     = names a ++ names b ++ names c
names (TSQUASH t)      = names t
names (TTRUNC t)       = names t
names (TCONST t)       = names t
names (SUBSING t)      = names t
names (DUM t)          = names t
names (FFDEFS t t₁)    = names t ++ names t₁
names PURE             = []
names (TERM t)         = names t
names (ENC t)          = names t
names (UNIV x)         = []
names (LIFT t)         = names t
names (LOWER t)        = names t
names (SHRINK t)       = names t



subv : Var → Term → Term → Term
subv v t (VAR x) with x ≟ v
... | yes _ = t
... | no _ = VAR x
subv v t NAT = NAT
subv v t QNAT = QNAT
subv v t TNAT = TNAT
subv v t (LT u u₁) = LT (subv v t u) (subv v t u₁)
subv v t (QLT u u₁) = QLT (subv v t u) (subv v t u₁)
subv v t (NUM x) = NUM x
subv v t (IFLT u u₁ u₂ u₃) = IFLT (subv v t u) (subv v t u₁) (subv v t u₂) (subv v t u₃)
subv v t (IFEQ u u₁ u₂ u₃) = IFEQ (subv v t u) (subv v t u₁) (subv v t u₂) (subv v t u₃)
subv v t (SUC u)      = SUC (subv v t u)
subv v t (PI u u₁)    = PI (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (LAMBDA u)   = LAMBDA (subv (suc v) (shiftUp 0 t) u)
subv v t (APPLY u u₁) = APPLY (subv v t u) (subv v t u₁)
subv v t (FIX u)      = FIX (subv v t u)
subv v t (LET u u₁)   = LET (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (WT u u₁)    = WT (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (SUP u u₁)   = SUP (subv v t u) (subv v t u₁)
--subv v t (DSUP u u₁)  = DSUP (subv v t u) (subv (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subv v t (WREC u u₁)  = WREC (subv v t u) (subv (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁)
subv v t (MT u u₁)    = MT (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
--subv v t (MSUP u u₁)  = MSUP (subv v t u) (subv v t u₁)
--subv v t (DMSUP u u₁) = DMSUP (subv v t u) (subv (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subv v t (SUM u u₁) = SUM (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (PAIR u u₁) = PAIR (subv v t u) (subv v t u₁)
subv v t (SPREAD u u₁) = SPREAD (subv v t u) (subv (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subv v t (SET u u₁) = SET (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (ISECT u u₁) = ISECT (subv v t u) (subv v t u₁)
subv v t (TUNION u u₁) = TUNION (subv v t u) (subv (suc v) (shiftUp 0 t) u₁)
subv v t (UNION u u₁) = UNION (subv v t u) (subv v t u₁)
subv v t (QTUNION u u₁) = QTUNION (subv v t u) (subv v t u₁)
subv v t (INL u) = INL (subv v t u)
subv v t (INR u) = INR (subv v t u)
subv v t (DECIDE u u₁ u₂) = DECIDE (subv v t u) (subv (suc v) (shiftUp 0 t) u₁) (subv (suc v) (shiftUp 0 t) u₂)
subv v t (EQ u u₁ u₂) = EQ (subv v t u) (subv v t u₁) (subv v t u₂)
subv v t (EQB u u₁ u₂ u₃) = EQB (subv v t u) (subv v t u₁) (subv v t u₂) (subv v t u₃)
subv v t AX = AX
subv v t FREE = FREE
subv v t (MSEQ x) = MSEQ x
subv v t (MAPP s u) = MAPP s (subv v t u)
subv v t (CS x) = CS x
subv v t (NAME x) = NAME x
subv v t (FRESH a) = FRESH (subv v (shiftNameUp 0 t) a)
subv v t (LOAD a) = LOAD a
subv v t (CHOOSE a b) = CHOOSE (subv v t a) (subv v t b)
--subv v t (IFC0 a t₁ t₂) = IFC0 (subv v t a) (subv v t t₁) (subv v t t₂)
subv v t (TSQUASH u) = TSQUASH (subv v t u)
subv v t (TTRUNC u) = TTRUNC (subv v t u)
subv v t (TCONST u) = TCONST (subv v t u)
subv v t (SUBSING u) = SUBSING (subv v t u)
subv v t (DUM u) = DUM (subv v t u)
subv v t (FFDEFS u u₁) = FFDEFS (subv v t u) (subv v t u₁)
subv v t PURE = PURE
subv v t (TERM u) = TERM (subv v t u)
subv v t (ENC u) = ENC u --(subv v t u) -- u is meant to be a closed term
subv v t (UNIV x) = UNIV x
subv v t (LIFT u) = LIFT (subv v t u)
subv v t (LOWER u) = LOWER (subv v t u)
subv v t (SHRINK u) = SHRINK (subv v t u)


-- substitute '0' for 't' in 'u'
sub : Term → Term → Term
sub t u = shiftDown 0 (subv 0 (shiftUp 0 t) u)


-- renames a name
renn : Name → Name → Term → Term
renn v t (VAR x) = VAR x
renn v t NAT = NAT
renn v t QNAT = QNAT
renn v t TNAT = TNAT
renn v t (LT u u₁) = LT (renn v t u) (renn v t u₁)
renn v t (QLT u u₁) = QLT (renn v t u) (renn v t u₁)
renn v t (NUM x) = NUM x
renn v t (IFLT u u₁ u₂ u₃) = IFLT (renn v t u) (renn v t u₁) (renn v t u₂) (renn v t u₃)
renn v t (IFEQ u u₁ u₂ u₃) = IFEQ (renn v t u) (renn v t u₁) (renn v t u₂) (renn v t u₃)
renn v t (SUC u) = SUC (renn v t u)
renn v t (PI u u₁) =  PI (renn v t u) (renn v t u₁)
renn v t (LAMBDA u) =  LAMBDA (renn v t u)
renn v t (APPLY u u₁) = APPLY (renn v t u) (renn v t u₁)
renn v t (FIX u) = FIX (renn v t u)
renn v t (LET u u₁) = LET (renn v t u) (renn v t u₁)
renn v t (WT u u₁) = WT (renn v t u) (renn v t u₁)
renn v t (SUP u u₁) = SUP (renn v t u) (renn v t u₁)
--renn v t (DSUP u u₁) = DSUP (renn v t u) (renn v t u₁)
renn v t (WREC u u₁) = WREC (renn v t u) (renn v t u₁)
renn v t (MT u u₁) = MT (renn v t u) (renn v t u₁)
--renn v t (MSUP u u₁) = MSUP (renn v t u) (renn v t u₁)
--renn v t (DMSUP u u₁) = DMSUP (renn v t u) (renn v t u₁)
renn v t (SUM u u₁) = SUM (renn v t u) (renn v t u₁)
renn v t (PAIR u u₁) = PAIR (renn v t u) (renn v t u₁)
renn v t (SPREAD u u₁) = SPREAD (renn v t u) (renn v t u₁)
renn v t (SET u u₁) = SET (renn v t u) (renn v t u₁)
renn v t (ISECT u u₁) = ISECT (renn v t u) (renn v t u₁)
renn v t (TUNION u u₁) = TUNION (renn v t u) (renn v t u₁)
renn v t (UNION u u₁) = UNION (renn v t u) (renn v t u₁)
renn v t (QTUNION u u₁) = QTUNION (renn v t u) (renn v t u₁)
renn v t (INL u) = INL (renn v t u)
renn v t (INR u) = INR (renn v t u)
renn v t (DECIDE u u₁ u₂) = DECIDE (renn v t u) (renn v t u₁) (renn v t u₂)
renn v t (EQ u u₁ u₂) = EQ (renn v t u) (renn v t u₁) (renn v t u₂)
renn v t (EQB u u₁ u₂ u₃) = EQB (renn v t u) (renn v t u₁) (renn v t u₂) (renn v t u₃)
renn v t AX = AX
renn v t (MSEQ x) = MSEQ x
renn v t (MAPP s u) = MAPP s (renn v t u)
renn v t FREE = FREE
renn v t (CS x) with x ≟ v
... | yes _ = CS t
... | no _ = CS x
renn v t (NAME x) with x ≟ v
... | yes _ = NAME t
... | no _ = NAME x
renn v t (FRESH a) = FRESH (renn (suc v) (suc t) a)
renn v t (LOAD a) = LOAD a
renn v t (CHOOSE a b) = CHOOSE (renn v t a) (renn v t b)
--renn v t (IFC0 a t₁ t₂) = IFC0 (renn v t a) (renn v t t₁) (renn v t t₂)
renn v t (TSQUASH u) = TSQUASH (renn v t u)
renn v t (TTRUNC u) = TTRUNC (renn v t u)
renn v t (TCONST u) = TCONST (renn v t u)
renn v t (SUBSING u) = SUBSING (renn v t u)
renn v t (DUM u) = DUM (renn v t u)
renn v t (FFDEFS u u₁) = FFDEFS (renn v t u) (renn v t u₁)
renn v t PURE = PURE
renn v t (TERM u) = TERM (renn v t u)
renn v t (ENC u) = ENC (renn v t u)
renn v t (UNIV x) = UNIV x
renn v t (LIFT u) = LIFT (renn v t u)
renn v t (LOWER u) = LOWER (renn v t u)
renn v t (SHRINK u) = SHRINK (renn v t u)


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


abstract
  subvNotIn : (v : Var) (t u : Term) → ¬ (v ∈ fvars u) → subv v t u ≡ u
  subvNotIn v t (VAR x) n with x ≟ v
  ... | yes p =  ⊥-elim (n (here (sym p)))
  ... | no p = refl
  subvNotIn v t NAT n = refl
  subvNotIn v t QNAT n = refl
  subvNotIn v t TNAT n = refl
  subvNotIn v t (LT u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  subvNotIn v t (QLT u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  subvNotIn v t (NUM x) n = refl
  subvNotIn v t (IFLT u u₁ u₂ u₃) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
            | subvNotIn v t u₂ (notInAppVars1 {v} {fvars u₂} {_} (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)))
            | subvNotIn v t u₃ (notInAppVars2 {v} {fvars u₂} {_} (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))) = refl
  subvNotIn v t (IFEQ u u₁ u₂ u₃) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
            | subvNotIn v t u₂ (notInAppVars1 {v} {fvars u₂} {_} (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)))
            | subvNotIn v t u₃ (notInAppVars2 {v} {fvars u₂} {_} (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))) = refl
  subvNotIn v t (SUC u) n
    rewrite subvNotIn v t u n = refl
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
  subvNotIn v t (WT u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
  subvNotIn v t (SUP u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  {--subvNotIn v t (DSUP u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ (inLowerVars _ _ j)))) = refl--}
  subvNotIn v t (WREC u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ (inLowerVars _ _ (inLowerVars _ _ j))))) = refl
  subvNotIn v t (MT u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
  {--subvNotIn v t (MSUP u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  subvNotIn v t (DMSUP u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ (inLowerVars _ _ j)))) = refl--}
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
  subvNotIn v t (ISECT u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  subvNotIn v t (TUNION u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn (suc v) (shiftUp 0 t) u₁ (λ j → ⊥-elim (notInAppVars2 n (inLowerVars _ _ j))) = refl
  subvNotIn v t (UNION u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  subvNotIn v t (QTUNION u u₁) n
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
  subvNotIn v t (EQB u u₁ u₂ u₃) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
            | subvNotIn v t u₂ (notInAppVars1 {v} {fvars u₂} {_} (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)))
            | subvNotIn v t u₃ (notInAppVars2 {v} {fvars u₂} {_} (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))) = refl
  subvNotIn v t AX n = refl
  subvNotIn v t FREE n = refl
  subvNotIn v t (MSEQ x) n = refl
  subvNotIn v t (MAPP s u) n
    rewrite subvNotIn v t u n = refl
  subvNotIn v t (CS x) n = refl
  subvNotIn v t (NAME x) n = refl
  subvNotIn v t (FRESH u) n
    rewrite subvNotIn v (shiftNameUp 0 t) u n = refl
  subvNotIn v t (LOAD u) n = refl
  --  rewrite subvNotIn v t u n = refl
  subvNotIn v t (CHOOSE u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars2 n) = refl
  {--subvNotIn v t (IFC0 u u₁ u₂) n
    rewrite subvNotIn v t u (notInAppVars1 n)
            | subvNotIn v t u₁ (notInAppVars1 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n))
            | subvNotIn v t u₂ (notInAppVars2 {v} {fvars u₁} {_} (notInAppVars2 {v} {fvars u} {_} n)) = refl--}
  subvNotIn v t (TSQUASH u) n
    rewrite subvNotIn v t u n = refl
  subvNotIn v t (TTRUNC u) n
    rewrite subvNotIn v t u n = refl
  subvNotIn v t (TCONST u) n
    rewrite subvNotIn v t u n = refl
  subvNotIn v t (SUBSING u) n
    rewrite subvNotIn v t u n = refl
  subvNotIn v t (DUM u) n
    rewrite subvNotIn v t u n = refl
  subvNotIn v t (FFDEFS u u₁) n
    rewrite subvNotIn v t u (notInAppVars1 n)
    rewrite subvNotIn v t u₁ (notInAppVars2 n) = refl
  subvNotIn v t PURE n = refl
  subvNotIn v t (TERM u) n rewrite subvNotIn v t u n = refl
  subvNotIn v t (ENC u) n = refl --rewrite subvNotIn v t u n = refl
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


abstract
  shiftDownTrivial : (v : Var) (u : Term) → ((w : Var) → v ≤ w → w # u) → shiftDown v u ≡ u
  shiftDownTrivial v (VAR 0) i = refl
  shiftDownTrivial v (VAR (suc x)) i with suc x ≤? v
  ... | yes z = refl
  ... | no z = ⊥-elim (i (suc x) (<⇒≤ (≰⇒> z)) (here refl)) --(i (suc x) (sucLeInj (≰⇒> z)) (here refl))
  shiftDownTrivial v NAT i = refl
  shiftDownTrivial v QNAT i = refl
  shiftDownTrivial v TNAT i = refl
  shiftDownTrivial v (LT u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
    rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (QLT u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
    rewrite shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (NUM x) i = refl
  shiftDownTrivial v (IFLT u u₁ u₂ u₃) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftDownTrivial v u₂ (impLeNotApp1 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftDownTrivial v u₃ (impLeNotApp2 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftDownTrivial v (IFEQ u u₁ u₂ u₃) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftDownTrivial v u₂ (impLeNotApp1 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftDownTrivial v u₃ (impLeNotApp2 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftDownTrivial v (SUC u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (PI u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftDownTrivial v (LAMBDA u) i
    rewrite shiftDownTrivial (suc v) u (impLeNotLower _ _ i) = refl
  shiftDownTrivial v (APPLY u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (FIX u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (LET u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftDownTrivial v (WT u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftDownTrivial v (SUP u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  {--shiftDownTrivial v (DSUP u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl--}
  shiftDownTrivial v (WREC u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc (suc (suc v))) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)))) = refl
  shiftDownTrivial v (MT u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  {--shiftDownTrivial v (MSUP u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (DMSUP u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl--}
  shiftDownTrivial v (SUM u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftDownTrivial v (PAIR u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (SPREAD u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl
  shiftDownTrivial v (SET u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftDownTrivial v (ISECT u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (TUNION u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftDownTrivial v (UNION u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (QTUNION u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v (INL u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (INR u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (DECIDE u u₁ u₂) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | lowerVarsApp (fvars u₁) (fvars u₂)
            | shiftDownTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp1 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftDownTrivial (suc v) u₂ (impLeNotLower _ _ (impLeNotApp2 v (lowerVars (fvars u₁)) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftDownTrivial v (EQ u u₁ u₂) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftDownTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl
  shiftDownTrivial v (EQB u u₁ u₂ u₃) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftDownTrivial v u₂ (impLeNotApp1 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftDownTrivial v u₃ (impLeNotApp2 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftDownTrivial v AX i = refl
  shiftDownTrivial v FREE i = refl
  shiftDownTrivial v (MSEQ x) i = refl
  shiftDownTrivial v (MAPP s u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (CS x) i = refl
  shiftDownTrivial v (NAME x) i = refl
  shiftDownTrivial v (FRESH u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (LOAD u) i = refl
  --  rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (CHOOSE u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  {--shiftDownTrivial v (IFC0 u u₁ u₂) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftDownTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl--}
  shiftDownTrivial v (TSQUASH u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (TTRUNC u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (TCONST u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (SUBSING u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (DUM u) i
    rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (FFDEFS u u₁) i
    rewrite shiftDownTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftDownTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftDownTrivial v PURE i = refl
  shiftDownTrivial v (TERM u) i rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (ENC u) i = refl --rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (UNIV x) i = refl
  shiftDownTrivial v (LIFT u) i rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (LOWER u) i rewrite shiftDownTrivial v u i = refl
  shiftDownTrivial v (SHRINK u) i rewrite shiftDownTrivial v u i = refl


abstract
  shiftUpTrivial : (v : Var) (u : Term) → ((w : Var) → v ≤ w → w # u) → shiftUp v u ≡ u
  shiftUpTrivial v (VAR x) i with x <? v
  ... | yes z = refl
  ... | no z = ⊥-elim (i x (sucLeInj (≰⇒> z)) (here refl))
  shiftUpTrivial v NAT i = refl
  shiftUpTrivial v QNAT i = refl
  shiftUpTrivial v TNAT i = refl
  shiftUpTrivial v (LT u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftUpTrivial v (QLT u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftUpTrivial v (NUM x) i = refl
  shiftUpTrivial v (IFLT u u₁ u₂ u₃) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftUpTrivial v u₂ (impLeNotApp1 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftUpTrivial v u₃ (impLeNotApp2 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftUpTrivial v (IFEQ u u₁ u₂ u₃) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftUpTrivial v u₂ (impLeNotApp1 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftUpTrivial v u₃ (impLeNotApp2 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftUpTrivial v (SUC u) i
    rewrite shiftUpTrivial v u i = refl
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
  shiftUpTrivial v (WT u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftUpTrivial v (SUP u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  {--shiftUpTrivial v (DSUP u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl--}
  shiftUpTrivial v (WREC u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial (suc (suc (suc v))) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)))) = refl
  shiftUpTrivial v (MT u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  {--shiftUpTrivial v (MSUP u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftUpTrivial v (DMSUP u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial (suc (suc v)) u₁ (impLeNotLower _ _ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i))) = refl--}
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
  shiftUpTrivial v (ISECT u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftUpTrivial v (TUNION u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial (suc v) u₁ (impLeNotLower _ _ (impLeNotApp2 _ _ _ i)) = refl
  shiftUpTrivial v (UNION u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftUpTrivial v (QTUNION u u₁) i
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
  shiftUpTrivial v (EQB u u₁ u₂ u₃) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftUpTrivial v u₂ (impLeNotApp1 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)))
            | shiftUpTrivial v u₃ (impLeNotApp2 v (fvars u₂) _ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))) = refl
  shiftUpTrivial v AX i = refl
  shiftUpTrivial v FREE i = refl
  shiftUpTrivial v (MSEQ x) i = refl
  shiftUpTrivial v (MAPP s u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (CS x) i = refl
  shiftUpTrivial v (NAME x) i = refl
  shiftUpTrivial v (FRESH u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (LOAD u) i = refl
  --  rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (CHOOSE u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  {--shiftUpTrivial v (IFC0 u u₁ u₂) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp1 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i))
            | shiftUpTrivial v u₂ (impLeNotApp2 v (fvars u₁) _ (impLeNotApp2 v (fvars u) _ i)) = refl--}
  shiftUpTrivial v (TSQUASH u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (TTRUNC u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (TCONST u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (SUBSING u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (DUM u) i
    rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (FFDEFS u u₁) i
    rewrite shiftUpTrivial v u (impLeNotApp1 _ _ _ i)
            | shiftUpTrivial v u₁ (impLeNotApp2 _ _ _ i) = refl
  shiftUpTrivial v PURE i = refl
  shiftUpTrivial v (TERM u) i rewrite shiftUpTrivial v u i = refl
  shiftUpTrivial v (ENC u) i = refl --rewrite shiftUpTrivial v u i = refl
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


abstract
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
  shiftDownUp TNAT n = refl
  shiftDownUp (LT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (QLT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (NUM x) n = refl
  shiftDownUp (IFLT t t₁ t₂ t₃) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n | shiftDownUp t₃ n = refl
  shiftDownUp (IFEQ t t₁ t₂ t₃) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n | shiftDownUp t₃ n = refl
  shiftDownUp (SUC t) n rewrite shiftDownUp t n = refl
  shiftDownUp (PI t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  shiftDownUp (LAMBDA t) n rewrite shiftDownUp t (suc n) = refl
  shiftDownUp (APPLY t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (FIX t) n rewrite shiftDownUp t n = refl
  shiftDownUp (LET t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  shiftDownUp (WT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  shiftDownUp (SUP t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  --shiftDownUp (DSUP t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc (suc n)) = refl
  shiftDownUp (WREC t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc (suc (suc n))) = refl
  shiftDownUp (MT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  --shiftDownUp (MSUP t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  --shiftDownUp (DMSUP t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc (suc n)) = refl
  shiftDownUp (SUM t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  shiftDownUp (PAIR t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (SPREAD t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc (suc n)) = refl
  shiftDownUp (SET t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  shiftDownUp (ISECT t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (TUNION t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) = refl
  shiftDownUp (UNION t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (QTUNION t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp (INL t) n rewrite shiftDownUp t n = refl
  shiftDownUp (INR t) n rewrite shiftDownUp t n = refl
  shiftDownUp (DECIDE t t₁ t₂) n rewrite shiftDownUp t n | shiftDownUp t₁ (suc n) | shiftDownUp t₂ (suc n) = refl
  shiftDownUp (EQ t t₁ t₂) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n = refl
  shiftDownUp (EQB t t₁ t₂ t₃) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n | shiftDownUp t₃ n = refl
  shiftDownUp AX n = refl
  shiftDownUp FREE n = refl
  shiftDownUp (MSEQ x) n = refl
  shiftDownUp (MAPP s t) n rewrite shiftDownUp t n = refl
  shiftDownUp (CS x) n = refl
  shiftDownUp (NAME x) n = refl
  shiftDownUp (FRESH t) n rewrite shiftDownUp t n = refl
  shiftDownUp (LOAD t) n rewrite shiftDownUp t n = refl
  shiftDownUp (CHOOSE t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  --shiftDownUp (IFC0 t t₁ t₂) n rewrite shiftDownUp t n | shiftDownUp t₁ n | shiftDownUp t₂ n = refl
  shiftDownUp (TSQUASH t) n rewrite shiftDownUp t n = refl
  shiftDownUp (TTRUNC t) n rewrite shiftDownUp t n = refl
  shiftDownUp (TCONST t) n rewrite shiftDownUp t n = refl
  shiftDownUp (SUBSING t) n rewrite shiftDownUp t n = refl
  shiftDownUp (DUM t) n rewrite shiftDownUp t n = refl
  shiftDownUp (FFDEFS t t₁) n rewrite shiftDownUp t n | shiftDownUp t₁ n = refl
  shiftDownUp PURE n = refl
  shiftDownUp (TERM t) n rewrite shiftDownUp t n = refl
  shiftDownUp (ENC t) n rewrite shiftDownUp t n = refl
  shiftDownUp (UNIV x) n = refl
  shiftDownUp (LIFT t) n rewrite shiftDownUp t n = refl
  shiftDownUp (LOWER t) n rewrite shiftDownUp t n = refl
  shiftDownUp (SHRINK t) n rewrite shiftDownUp t n = refl


is-NUM : (t : Term) → (Σ ℕ (λ n → t ≡ NUM n)) ⊎ ((n : ℕ) → ¬ t ≡ NUM n)
is-NUM (VAR x) = inj₂ (λ { n () })
is-NUM NAT = inj₂ (λ { n () })
is-NUM QNAT = inj₂ (λ { n () })
is-NUM TNAT = inj₂ (λ { n () })
is-NUM (LT t t₁) = inj₂ (λ { n () })
is-NUM (QLT t t₁) = inj₂ (λ { n () })
is-NUM (NUM x) = inj₁ ( x , refl)
is-NUM (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-NUM (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-NUM (SUC t) = inj₂ (λ { n () })
is-NUM (PI t t₁) = inj₂ (λ { n () })
is-NUM (LAMBDA t) = inj₂ (λ { n () })
is-NUM (APPLY t t₁) = inj₂ (λ { n () })
is-NUM (FIX t) = inj₂ (λ { n () })
is-NUM (LET t t₁) = inj₂ (λ { n () })
is-NUM (WT t t₁) = inj₂ (λ { n () })
is-NUM (SUP t t₁) = inj₂ (λ { n () })
--is-NUM (DSUP t t₁) = inj₂ (λ { n () })
is-NUM (WREC t t₁) = inj₂ (λ { n () })
is-NUM (MT t t₁) = inj₂ (λ { n () })
--is-NUM (MSUP t t₁) = inj₂ (λ { n () })
--is-NUM (DMSUP t t₁) = inj₂ (λ { n () })
is-NUM (SUM t t₁) = inj₂ (λ { n () })
is-NUM (PAIR t t₁) = inj₂ (λ { n () })
is-NUM (SPREAD t t₁) = inj₂ (λ { n () })
is-NUM (SET t t₁) = inj₂ (λ { n () })
is-NUM (ISECT t t₁) = inj₂ (λ { n () })
is-NUM (TUNION t t₁) = inj₂ (λ { n () })
is-NUM (UNION t t₁) = inj₂ (λ { n () })
is-NUM (QTUNION t t₁) = inj₂ (λ { n () })
is-NUM (INL t) = inj₂ (λ { n () })
is-NUM (INR t) = inj₂ (λ { n () })
is-NUM (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-NUM (EQ t t₁ t₂) = inj₂ (λ { n () })
is-NUM (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-NUM AX = inj₂ (λ { n () })
is-NUM FREE = inj₂ (λ { n () })
is-NUM (MSEQ x) = inj₂ (λ { n () })
is-NUM (MAPP s t) = inj₂ (λ { n () })
is-NUM (CS x) = inj₂ (λ { n () })
is-NUM (NAME x) = inj₂ (λ { n () })
is-NUM (FRESH t) = inj₂ (λ { n () })
is-NUM (LOAD t) = inj₂ (λ { n () })
is-NUM (CHOOSE t t₁) = inj₂ (λ { n () })
--is-NUM (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-NUM (TSQUASH t) = inj₂ (λ { n () })
is-NUM (TTRUNC t) = inj₂ (λ { n () })
is-NUM (TCONST t) = inj₂ (λ { n () })
is-NUM (SUBSING t) = inj₂ (λ { n () })
is-NUM (DUM t) = inj₂ (λ { n () })
is-NUM (FFDEFS t t₁) = inj₂ (λ { n () })
is-NUM PURE = inj₂ (λ { n () })
is-NUM (TERM t) = inj₂ (λ { n () })
is-NUM (ENC t) = inj₂ (λ { n () })
is-NUM (UNIV x) = inj₂ (λ { n () })
is-NUM (LIFT t) = inj₂ (λ { n () })
is-NUM (LOWER t) = inj₂ (λ { n () })
is-NUM (SHRINK t) = inj₂ (λ { n () })


is-LAM : (t : Term) → (Σ Term (λ u → t ≡ LAMBDA u)) ⊎ ((u : Term) → ¬ t ≡ LAMBDA u)
is-LAM (VAR x) = inj₂ (λ { n () })
is-LAM NAT = inj₂ (λ { n () })
is-LAM QNAT = inj₂ (λ { n () })
is-LAM TNAT = inj₂ (λ { n () })
is-LAM (LT t t₁) = inj₂ (λ { n () })
is-LAM (QLT t t₁) = inj₂ (λ { n () })
is-LAM (NUM x) = inj₂ (λ { n () })
is-LAM (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-LAM (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-LAM (SUC t) = inj₂ (λ { n () })
is-LAM (PI t t₁) = inj₂ (λ { n () })
is-LAM (LAMBDA t) = inj₁ (t , refl)
is-LAM (APPLY t t₁) = inj₂ (λ { n () })
is-LAM (FIX t) = inj₂ (λ { n () })
is-LAM (LET t t₁) = inj₂ (λ { n () })
is-LAM (WT t t₁) = inj₂ (λ { n () })
is-LAM (SUP t t₁) = inj₂ (λ { n () })
--is-LAM (DSUP t t₁) = inj₂ (λ { n () })
is-LAM (WREC t t₁) = inj₂ (λ { n () })
is-LAM (MT t t₁) = inj₂ (λ { n () })
--is-LAM (MSUP t t₁) = inj₂ (λ { n () })
--is-LAM (DMSUP t t₁) = inj₂ (λ { n () })
is-LAM (SUM t t₁) = inj₂ (λ { n () })
is-LAM (PAIR t t₁) = inj₂ (λ { n () })
is-LAM (SPREAD t t₁) = inj₂ (λ { n () })
is-LAM (SET t t₁) = inj₂ (λ { n () })
is-LAM (ISECT t t₁) = inj₂ (λ { n () })
is-LAM (TUNION t t₁) = inj₂ (λ { n () })
is-LAM (UNION t t₁) = inj₂ (λ { n () })
is-LAM (QTUNION t t₁) = inj₂ (λ { n () })
is-LAM (INL t) = inj₂ (λ { n () })
is-LAM (INR t) = inj₂ (λ { n () })
is-LAM (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-LAM (EQ t t₁ t₂) = inj₂ (λ { n () })
is-LAM (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-LAM AX = inj₂ (λ { n () })
is-LAM FREE = inj₂ (λ { n () })
is-LAM (MSEQ x) = inj₂ (λ { n () })
is-LAM (MAPP s t) = inj₂ (λ { n () })
is-LAM (CS x) = inj₂ (λ { n () })
is-LAM (NAME x) = inj₂ (λ { n () })
is-LAM (FRESH t) = inj₂ (λ { n () })
is-LAM (LOAD t) = inj₂ (λ { n () })
is-LAM (CHOOSE t t₁) = inj₂ (λ { n () })
--is-LAM (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-LAM (TSQUASH t) = inj₂ (λ { n () })
is-LAM (TTRUNC t) = inj₂ (λ { n () })
is-LAM (TCONST t) = inj₂ (λ { n () })
is-LAM (SUBSING t) = inj₂ (λ { n () })
is-LAM (DUM t) = inj₂ (λ { n () })
is-LAM (FFDEFS t t₁) = inj₂ (λ { n () })
is-LAM PURE = inj₂ (λ { n () })
is-LAM (TERM t) = inj₂ (λ { n () })
is-LAM (ENC t) = inj₂ (λ { n () })
is-LAM (UNIV x) = inj₂ (λ { n () })
is-LAM (LIFT t) = inj₂ (λ { n () })
is-LAM (LOWER t) = inj₂ (λ { n () })
is-LAM (SHRINK t) = inj₂ (λ { n () })


is-CS : (t : Term) → (Σ Name (λ n → t ≡ CS n)) ⊎ ((n : Name) → ¬ t ≡ CS n)
is-CS (VAR x) = inj₂ (λ { n () })
is-CS NAT = inj₂ (λ { n () })
is-CS QNAT = inj₂ (λ { n () })
is-CS TNAT = inj₂ (λ { n () })
is-CS (LT t t₁) = inj₂ (λ { n () })
is-CS (QLT t t₁) = inj₂ (λ { n () })
is-CS (NUM x) = inj₂ (λ { n () })
is-CS (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-CS (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-CS (SUC t) = inj₂ (λ { n () })
is-CS (PI t t₁) = inj₂ (λ { n () })
is-CS (LAMBDA t) = inj₂ (λ { n () })
is-CS (APPLY t t₁) = inj₂ (λ { n () })
is-CS (FIX t) = inj₂ (λ { n () })
is-CS (LET t t₁) = inj₂ (λ { n () })
is-CS (WT t t₁) = inj₂ (λ { n () })
is-CS (SUP t t₁) = inj₂ (λ { n () })
--is-CS (DSUP t t₁) = inj₂ (λ { n () })
is-CS (WREC t t₁) = inj₂ (λ { n () })
is-CS (MT t t₁) = inj₂ (λ { n () })
--is-CS (MSUP t t₁) = inj₂ (λ { n () })
--is-CS (DMSUP t t₁) = inj₂ (λ { n () })
is-CS (SUM t t₁) = inj₂ (λ { n () })
is-CS (PAIR t t₁) = inj₂ (λ { n () })
is-CS (SPREAD t t₁) = inj₂ (λ { n () })
is-CS (SET t t₁) = inj₂ (λ { n () })
is-CS (ISECT t t₁) = inj₂ (λ { n () })
is-CS (TUNION t t₁) = inj₂ (λ { n () })
is-CS (UNION t t₁) = inj₂ (λ { n () })
is-CS (QTUNION t t₁) = inj₂ (λ { n () })
is-CS (INL t) = inj₂ (λ { n () })
is-CS (INR t) = inj₂ (λ { n () })
is-CS (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-CS (EQ t t₁ t₂) = inj₂ (λ { n () })
is-CS (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-CS AX = inj₂ (λ { n () })
is-CS FREE = inj₂ (λ { n () })
is-CS (MSEQ x) = inj₂ (λ { n () })
is-CS (MAPP s t) = inj₂ (λ { n () })
is-CS (CS x) = inj₁ (x , refl)
is-CS (NAME x) = inj₂ (λ { n () })
is-CS (FRESH t) = inj₂ (λ { n () })
is-CS (LOAD t) = inj₂ (λ { n () })
is-CS (CHOOSE t t₁) = inj₂ (λ { n () })
--is-CS (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-CS (TSQUASH t) = inj₂ (λ { n () })
is-CS (TTRUNC t) = inj₂ (λ { n () })
is-CS (TCONST t) = inj₂ (λ { n () })
is-CS (SUBSING t) = inj₂ (λ { n () })
is-CS (DUM t) = inj₂ (λ { n () })
is-CS (FFDEFS t t₁) = inj₂ (λ { n () })
is-CS PURE = inj₂ (λ { n () })
is-CS (TERM t) = inj₂ (λ { n () })
is-CS (ENC t) = inj₂ (λ { n () })
is-CS (UNIV x) = inj₂ (λ { n () })
is-CS (LIFT t) = inj₂ (λ { n () })
is-CS (LOWER t) = inj₂ (λ { n () })
is-CS (SHRINK t) = inj₂ (λ { n () })


is-NAME : (t : Term) → (Σ Name (λ n → t ≡ NAME n)) ⊎ ((n : Name) → ¬ t ≡ NAME n)
is-NAME (VAR x) = inj₂ (λ { n () })
is-NAME NAT = inj₂ (λ { n () })
is-NAME QNAT = inj₂ (λ { n () })
is-NAME TNAT = inj₂ (λ { n () })
is-NAME (LT t t₁) = inj₂ (λ { n () })
is-NAME (QLT t t₁) = inj₂ (λ { n () })
is-NAME (NUM x) = inj₂ (λ { n () })
is-NAME (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-NAME (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-NAME (SUC t) = inj₂ (λ { n () })
is-NAME (PI t t₁) = inj₂ (λ { n () })
is-NAME (LAMBDA t) = inj₂ (λ { n () })
is-NAME (APPLY t t₁) = inj₂ (λ { n () })
is-NAME (FIX t) = inj₂ (λ { n () })
is-NAME (LET t t₁) = inj₂ (λ { n () })
is-NAME (WT t t₁) = inj₂ (λ { n () })
is-NAME (SUP t t₁) = inj₂ (λ { n () })
--is-NAME (DSUP t t₁) = inj₂ (λ { n () })
is-NAME (WREC t t₁) = inj₂ (λ { n () })
is-NAME (MT t t₁) = inj₂ (λ { n () })
--is-NAME (MSUP t t₁) = inj₂ (λ { n () })
--is-NAME (DMSUP t t₁) = inj₂ (λ { n () })
is-NAME (SUM t t₁) = inj₂ (λ { n () })
is-NAME (PAIR t t₁) = inj₂ (λ { n () })
is-NAME (SPREAD t t₁) = inj₂ (λ { n () })
is-NAME (SET t t₁) = inj₂ (λ { n () })
is-NAME (ISECT t t₁) = inj₂ (λ { n () })
is-NAME (TUNION t t₁) = inj₂ (λ { n () })
is-NAME (UNION t t₁) = inj₂ (λ { n () })
is-NAME (QTUNION t t₁) = inj₂ (λ { n () })
is-NAME (INL t) = inj₂ (λ { n () })
is-NAME (INR t) = inj₂ (λ { n () })
is-NAME (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-NAME (EQ t t₁ t₂) = inj₂ (λ { n () })
is-NAME (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-NAME AX = inj₂ (λ { n () })
is-NAME FREE = inj₂ (λ { n () })
is-NAME (MSEQ x) = inj₂ (λ { n () })
is-NAME (MAPP s t) = inj₂ (λ { n () })
is-NAME (CS x) = inj₂ (λ { n () })
is-NAME (NAME x) = inj₁ (x , refl)
is-NAME (FRESH t) = inj₂ (λ { n () })
is-NAME (LOAD t) = inj₂ (λ { n () })
is-NAME (CHOOSE t t₁) = inj₂ (λ { n () })
--is-NAME (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-NAME (TSQUASH t) = inj₂ (λ { n () })
is-NAME (TTRUNC t) = inj₂ (λ { n () })
is-NAME (TCONST t) = inj₂ (λ { n () })
is-NAME (SUBSING t) = inj₂ (λ { n () })
is-NAME (DUM t) = inj₂ (λ { n () })
is-NAME (FFDEFS t t₁) = inj₂ (λ { n () })
is-NAME PURE = inj₂ (λ { n () })
is-NAME (TERM t) = inj₂ (λ { n () })
is-NAME (ENC t) = inj₂ (λ { n () })
is-NAME (UNIV x) = inj₂ (λ { n () })
is-NAME (LIFT t) = inj₂ (λ { n () })
is-NAME (LOWER t) = inj₂ (λ { n () })
is-NAME (SHRINK t) = inj₂ (λ { n () })


is-MSEQ : (t : Term) → (Σ 𝕊 (λ n → t ≡ MSEQ n)) ⊎ ((n : 𝕊) → ¬ t ≡ MSEQ n)
is-MSEQ (VAR x) = inj₂ (λ { n () })
is-MSEQ NAT = inj₂ (λ { n () })
is-MSEQ QNAT = inj₂ (λ { n () })
is-MSEQ TNAT = inj₂ (λ { n () })
is-MSEQ (LT t t₁) = inj₂ (λ { n () })
is-MSEQ (QLT t t₁) = inj₂ (λ { n () })
is-MSEQ (NUM x) = inj₂ (λ { n () })
is-MSEQ (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-MSEQ (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-MSEQ (SUC t) = inj₂ (λ { n () })
is-MSEQ (PI t t₁) = inj₂ (λ { n () })
is-MSEQ (LAMBDA t) = inj₂ (λ { n () })
is-MSEQ (APPLY t t₁) = inj₂ (λ { n () })
is-MSEQ (FIX t) = inj₂ (λ { n () })
is-MSEQ (LET t t₁) = inj₂ (λ { n () })
is-MSEQ (WT t t₁) = inj₂ (λ { n () })
is-MSEQ (SUP t t₁) = inj₂ (λ { n () })
--is-MSEQ (DSUP t t₁) = inj₂ (λ { n () })
is-MSEQ (WREC t t₁) = inj₂ (λ { n () })
is-MSEQ (MT t t₁) = inj₂ (λ { n () })
--is-MSEQ (MSUP t t₁) = inj₂ (λ { n () })
--is-MSEQ (DMSUP t t₁) = inj₂ (λ { n () })
is-MSEQ (SUM t t₁) = inj₂ (λ { n () })
is-MSEQ (PAIR t t₁) = inj₂ (λ { n () })
is-MSEQ (SPREAD t t₁) = inj₂ (λ { n () })
is-MSEQ (SET t t₁) = inj₂ (λ { n () })
is-MSEQ (ISECT t t₁) = inj₂ (λ { n () })
is-MSEQ (TUNION t t₁) = inj₂ (λ { n () })
is-MSEQ (UNION t t₁) = inj₂ (λ { n () })
is-MSEQ (QTUNION t t₁) = inj₂ (λ { n () })
is-MSEQ (INL t) = inj₂ (λ { n () })
is-MSEQ (INR t) = inj₂ (λ { n () })
is-MSEQ (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-MSEQ (EQ t t₁ t₂) = inj₂ (λ { n () })
is-MSEQ (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-MSEQ AX = inj₂ (λ { n () })
is-MSEQ FREE = inj₂ (λ { n () })
is-MSEQ (MSEQ x) = inj₁ (x , refl)
is-MSEQ (MAPP s t) = inj₂ (λ { n () })
is-MSEQ (CS x) = inj₂ (λ { n () })
is-MSEQ (NAME x) = inj₂ (λ { n () })
is-MSEQ (FRESH t) = inj₂ (λ { n () })
is-MSEQ (LOAD t) = inj₂ (λ { n () })
is-MSEQ (CHOOSE t t₁) = inj₂ (λ { n () })
--is-MSEQ (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-MSEQ (TSQUASH t) = inj₂ (λ { n () })
is-MSEQ (TTRUNC t) = inj₂ (λ { n () })
is-MSEQ (TCONST t) = inj₂ (λ { n () })
is-MSEQ (SUBSING t) = inj₂ (λ { n () })
is-MSEQ (DUM t) = inj₂ (λ { n () })
is-MSEQ (FFDEFS t t₁) = inj₂ (λ { n () })
is-MSEQ PURE = inj₂ (λ { n () })
is-MSEQ (TERM t) = inj₂ (λ { n () })
is-MSEQ (ENC t) = inj₂ (λ { n () })
is-MSEQ (UNIV x) = inj₂ (λ { n () })
is-MSEQ (LIFT t) = inj₂ (λ { n () })
is-MSEQ (LOWER t) = inj₂ (λ { n () })
is-MSEQ (SHRINK t) = inj₂ (λ { n () })


is-PAIR : (t : Term) → (Σ Term (λ a → Σ Term (λ b → t ≡ PAIR a b))) ⊎ ((a b : Term) → ¬ t ≡ PAIR a b)
is-PAIR (VAR x) = inj₂ (λ { n m () })
is-PAIR NAT = inj₂ (λ { n m () })
is-PAIR QNAT = inj₂ (λ { n m () })
is-PAIR TNAT = inj₂ (λ { n m () })
is-PAIR (LT t t₁) = inj₂ (λ { n m () })
is-PAIR (QLT t t₁) = inj₂ (λ { n m () })
is-PAIR (NUM x) = inj₂ (λ { n m () })
is-PAIR (IFLT t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-PAIR (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-PAIR (SUC t) = inj₂ (λ { n m () })
is-PAIR (PI t t₁) = inj₂ (λ { n m () })
is-PAIR (LAMBDA t) = inj₂ (λ { n m () })
is-PAIR (APPLY t t₁) = inj₂ (λ { n m () })
is-PAIR (FIX t) = inj₂ (λ { n m () })
is-PAIR (LET t t₁) = inj₂ (λ { n m () })
is-PAIR (WT t t₁) = inj₂ (λ { n m () })
is-PAIR (SUP t t₁) = inj₂ (λ { n m () })
--is-PAIR (DSUP t t₁) = inj₂ (λ { n m () })
is-PAIR (WREC t t₁) = inj₂ (λ { n m () })
is-PAIR (MT t t₁) = inj₂ (λ { n m () })
--is-PAIR (MSUP t t₁) = inj₂ (λ { n m () })
--is-PAIR (DMSUP t t₁) = inj₂ (λ { n m () })
is-PAIR (SUM t t₁) = inj₂ (λ { n m () })
is-PAIR (PAIR t t₁) = inj₁ (t , t₁ , refl)
is-PAIR (SPREAD t t₁) = inj₂ (λ { n m () })
is-PAIR (SET t t₁) = inj₂ (λ { n m () })
is-PAIR (ISECT t t₁) = inj₂ (λ { n m () })
is-PAIR (TUNION t t₁) = inj₂ (λ { n m () })
is-PAIR (UNION t t₁) = inj₂ (λ { n m () })
is-PAIR (QTUNION t t₁) = inj₂ (λ { n m () })
is-PAIR (INL t) = inj₂ (λ { n m () })
is-PAIR (INR t) = inj₂ (λ { n m () })
is-PAIR (DECIDE t t₁ t₂) = inj₂ (λ { n m () })
is-PAIR (EQ t t₁ t₂) = inj₂ (λ { n m () })
is-PAIR (EQB t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-PAIR AX = inj₂ (λ { n m () })
is-PAIR FREE = inj₂ (λ { n m () })
is-PAIR (MSEQ x) = inj₂ (λ { n m () })
is-PAIR (MAPP s t) = inj₂ (λ { n m () })
is-PAIR (CS x) = inj₂ (λ { n m () })
is-PAIR (NAME x) = inj₂ (λ { n m () })
is-PAIR (FRESH t) = inj₂ (λ { n m () })
is-PAIR (LOAD t) = inj₂ (λ { n m () })
is-PAIR (CHOOSE t t₁) = inj₂ (λ { n m () })
--is-PAIR (IFC0 t t₁ t₂) = inj₂ (λ { n m () })
is-PAIR (TSQUASH t) = inj₂ (λ { n m () })
is-PAIR (TTRUNC t) = inj₂ (λ { n m () })
is-PAIR (TCONST t) = inj₂ (λ { n m () })
is-PAIR (SUBSING t) = inj₂ (λ { n m () })
is-PAIR (DUM t) = inj₂ (λ { n m () })
is-PAIR (FFDEFS t t₁) = inj₂ (λ { n m () })
is-PAIR PURE = inj₂ (λ { n m () })
is-PAIR (TERM t) = inj₂ (λ { n m () })
is-PAIR (ENC t) = inj₂ (λ { n m () })
is-PAIR (UNIV x) = inj₂ (λ { n m () })
is-PAIR (LIFT t) = inj₂ (λ { n m () })
is-PAIR (LOWER t) = inj₂ (λ { n m () })
is-PAIR (SHRINK t) = inj₂ (λ { n m () })


is-SUP : (t : Term) → (Σ Term (λ a → Σ Term (λ b → t ≡ SUP a b))) ⊎ ((a b : Term) → ¬ t ≡ SUP a b)
is-SUP (VAR x) = inj₂ (λ { n m () })
is-SUP NAT = inj₂ (λ { n m () })
is-SUP QNAT = inj₂ (λ { n m () })
is-SUP TNAT = inj₂ (λ { n m () })
is-SUP (LT t t₁) = inj₂ (λ { n m () })
is-SUP (QLT t t₁) = inj₂ (λ { n m () })
is-SUP (NUM x) = inj₂ (λ { n m () })
is-SUP (IFLT t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-SUP (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-SUP (SUC t) = inj₂ (λ { n m () })
is-SUP (PI t t₁) = inj₂ (λ { n m () })
is-SUP (LAMBDA t) = inj₂ (λ { n m () })
is-SUP (APPLY t t₁) = inj₂ (λ { n m () })
is-SUP (FIX t) = inj₂ (λ { n m () })
is-SUP (LET t t₁) = inj₂ (λ { n m () })
is-SUP (WT t t₁) = inj₂ (λ { n m () })
is-SUP (SUP t t₁) = inj₁ (t , t₁ , refl)
--is-SUP (DSUP t t₁) = inj₂ (λ { n m () })
is-SUP (WREC t t₁) = inj₂ (λ { n m () })
is-SUP (MT t t₁) = inj₂ (λ { n m () })
--is-SUP (MSUP t t₁) = inj₂ (λ { n m () })
--is-SUP (DMSUP t t₁) = inj₂ (λ { n m () })
is-SUP (SUM t t₁) = inj₂ (λ { n m () })
is-SUP (PAIR t t₁) = inj₂ (λ { n m () })
is-SUP (SPREAD t t₁) = inj₂ (λ { n m () })
is-SUP (SET t t₁) = inj₂ (λ { n m () })
is-SUP (ISECT t t₁) = inj₂ (λ { n m () })
is-SUP (TUNION t t₁) = inj₂ (λ { n m () })
is-SUP (UNION t t₁) = inj₂ (λ { n m () })
is-SUP (QTUNION t t₁) = inj₂ (λ { n m () })
is-SUP (INL t) = inj₂ (λ { n m () })
is-SUP (INR t) = inj₂ (λ { n m () })
is-SUP (DECIDE t t₁ t₂) = inj₂ (λ { n m () })
is-SUP (EQ t t₁ t₂) = inj₂ (λ { n m () })
is-SUP (EQB t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-SUP AX = inj₂ (λ { n m () })
is-SUP FREE = inj₂ (λ { n m () })
is-SUP (MSEQ x) = inj₂ (λ { n m () })
is-SUP (MAPP s t) = inj₂ (λ { n m () })
is-SUP (CS x) = inj₂ (λ { n m () })
is-SUP (NAME x) = inj₂ (λ { n m () })
is-SUP (FRESH t) = inj₂ (λ { n m () })
is-SUP (LOAD t) = inj₂ (λ { n m () })
is-SUP (CHOOSE t t₁) = inj₂ (λ { n m () })
--is-SUP (IFC0 t t₁ t₂) = inj₂ (λ { n m () })
is-SUP (TSQUASH t) = inj₂ (λ { n m () })
is-SUP (TTRUNC t) = inj₂ (λ { n m () })
is-SUP (TCONST t) = inj₂ (λ { n m () })
is-SUP (SUBSING t) = inj₂ (λ { n m () })
is-SUP (DUM t) = inj₂ (λ { n m () })
is-SUP (FFDEFS t t₁) = inj₂ (λ { n m () })
is-SUP PURE = inj₂ (λ { n m () })
is-SUP (TERM t) = inj₂ (λ { n m () })
is-SUP (ENC t) = inj₂ (λ { n m () })
is-SUP (UNIV x) = inj₂ (λ { n m () })
is-SUP (LIFT t) = inj₂ (λ { n m () })
is-SUP (LOWER t) = inj₂ (λ { n m () })
is-SUP (SHRINK t) = inj₂ (λ { n m () })


{--
is-MSUP : (t : Term) → (Σ Term (λ a → Σ Term (λ b → t ≡ MSUP a b))) ⊎ ((a b : Term) → ¬ t ≡ MSUP a b)
is-MSUP (VAR x) = inj₂ (λ { n m () })
is-MSUP NAT = inj₂ (λ { n m () })
is-MSUP QNAT = inj₂ (λ { n m () })
is-MSUP TNAT = inj₂ (λ { n m () })
is-MSUP (LT t t₁) = inj₂ (λ { n m () })
is-MSUP (QLT t t₁) = inj₂ (λ { n m () })
is-MSUP (NUM x) = inj₂ (λ { n m () })
is-MSUP (IFLT t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-MSUP (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-MSUP (SUC t) = inj₂ (λ { n m () })
is-MSUP (PI t t₁) = inj₂ (λ { n m () })
is-MSUP (LAMBDA t) = inj₂ (λ { n m () })
is-MSUP (APPLY t t₁) = inj₂ (λ { n m () })
is-MSUP (FIX t) = inj₂ (λ { n m () })
is-MSUP (LET t t₁) = inj₂ (λ { n m () })
is-MSUP (WT t t₁) = inj₂ (λ { n m () })
is-MSUP (SUP t t₁) = inj₂ (λ { n m () })
is-MSUP (DSUP t t₁) = inj₂ (λ { n m () })
is-MSUP (WREC t t₁) = inj₂ (λ { n m () })
is-MSUP (MT t t₁) = inj₂ (λ { n m () })
is-MSUP (MSUP t t₁) = inj₁ (t , t₁ , refl)
is-MSUP (DMSUP t t₁) = inj₂ (λ { n m () })
is-MSUP (SUM t t₁) = inj₂ (λ { n m () })
is-MSUP (PAIR t t₁) = inj₂ (λ { n m () })
is-MSUP (SPREAD t t₁) = inj₂ (λ { n m () })
is-MSUP (SET t t₁) = inj₂ (λ { n m () })
is-MSUP (ISECT t t₁) = inj₂ (λ { n m () })
is-MSUP (TUNION t t₁) = inj₂ (λ { n m () })
is-MSUP (UNION t t₁) = inj₂ (λ { n m () })
is-MSUP (QTUNION t t₁) = inj₂ (λ { n m () })
is-MSUP (INL t) = inj₂ (λ { n m () })
is-MSUP (INR t) = inj₂ (λ { n m () })
is-MSUP (DECIDE t t₁ t₂) = inj₂ (λ { n m () })
is-MSUP (EQ t t₁ t₂) = inj₂ (λ { n m () })
is-MSUP (EQB t t₁ t₂ t₃) = inj₂ (λ { n m () })
is-MSUP AX = inj₂ (λ { n m () })
is-MSUP FREE = inj₂ (λ { n m () })
is-MSUP (MSEQ x) = inj₂ (λ { n m () })
is-MSUP (MAPP s t) = inj₂ (λ { n m () })
is-MSUP (CS x) = inj₂ (λ { n m () })
is-MSUP (NAME x) = inj₂ (λ { n m () })
is-MSUP (FRESH t) = inj₂ (λ { n m () })
is-MSUP (LOAD t) = inj₂ (λ { n m () })
is-MSUP (CHOOSE t t₁) = inj₂ (λ { n m () })
--is-MSUP (IFC0 t t₁ t₂) = inj₂ (λ { n m () })
is-MSUP (TSQUASH t) = inj₂ (λ { n m () })
is-MSUP (TTRUNC t) = inj₂ (λ { n m () })
is-MSUP (TCONST t) = inj₂ (λ { n m () })
is-MSUP (SUBSING t) = inj₂ (λ { n m () })
is-MSUP (DUM t) = inj₂ (λ { n m () })
is-MSUP (FFDEFS t t₁) = inj₂ (λ { n m () })
is-MSUP PURE = inj₂ (λ { n m () })
is-MSUP (TERM t) = inj₂ (λ { n m () })
is-MSUP (ENC t) = inj₂ (λ { n m () })
is-MSUP (UNIV x) = inj₂ (λ { n m () })
is-MSUP (LIFT t) = inj₂ (λ { n m () })
is-MSUP (LOWER t) = inj₂ (λ { n m () })
is-MSUP (SHRINK t) = inj₂ (λ { n m () })
--}


is-INL : (t : Term) → (Σ Term (λ u → t ≡ INL u)) ⊎ ((u : Term) → ¬ t ≡ INL u)
is-INL (VAR x) = inj₂ (λ { n () })
is-INL NAT = inj₂ (λ { n () })
is-INL QNAT = inj₂ (λ { n () })
is-INL TNAT = inj₂ (λ { n () })
is-INL (LT t t₁) = inj₂ (λ { n () })
is-INL (QLT t t₁) = inj₂ (λ { n () })
is-INL (NUM x) = inj₂ (λ { n () })
is-INL (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-INL (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-INL (SUC t) = inj₂ (λ { n () })
is-INL (PI t t₁) = inj₂ (λ { n () })
is-INL (LAMBDA t) = inj₂ (λ { n () })
is-INL (APPLY t t₁) = inj₂ (λ { n () })
is-INL (FIX t) = inj₂ (λ { n () })
is-INL (LET t t₁) = inj₂ (λ { n () })
is-INL (WT t t₁) = inj₂ (λ { n () })
is-INL (SUP t t₁) = inj₂ (λ { n () })
--is-INL (DSUP t t₁) = inj₂ (λ { n () })
is-INL (WREC t t₁) = inj₂ (λ { n () })
is-INL (MT t t₁) = inj₂ (λ { n () })
--is-INL (MSUP t t₁) = inj₂ (λ { n () })
--is-INL (DMSUP t t₁) = inj₂ (λ { n () })
is-INL (SUM t t₁) = inj₂ (λ { n () })
is-INL (PAIR t t₁) = inj₂ (λ { n () })
is-INL (SPREAD t t₁) = inj₂ (λ { n () })
is-INL (SET t t₁) = inj₂ (λ { n () })
is-INL (ISECT t t₁) = inj₂ (λ { n () })
is-INL (TUNION t t₁) = inj₂ (λ { n () })
is-INL (UNION t t₁) = inj₂ (λ { n () })
is-INL (QTUNION t t₁) = inj₂ (λ { n () })
is-INL (INL t) = inj₁ (t , refl)
is-INL (INR t) = inj₂ (λ { n () })
is-INL (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-INL (EQ t t₁ t₂) = inj₂ (λ { n () })
is-INL (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-INL AX = inj₂ (λ { n () })
is-INL FREE = inj₂ (λ { n () })
is-INL (MSEQ x) = inj₂ (λ { n () })
is-INL (MAPP s t) = inj₂ (λ { n () })
is-INL (CS x) = inj₂ (λ { n () })
is-INL (NAME x) = inj₂ (λ { n () })
is-INL (FRESH t) = inj₂ (λ { n () })
is-INL (LOAD t) = inj₂ (λ { n () })
is-INL (CHOOSE t t₁) = inj₂ (λ { n () })
--is-INL (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-INL (TSQUASH t) = inj₂ (λ { n () })
is-INL (TTRUNC t) = inj₂ (λ { n () })
is-INL (TCONST t) = inj₂ (λ { n () })
is-INL (SUBSING t) = inj₂ (λ { n () })
is-INL (DUM t) = inj₂ (λ { n () })
is-INL (FFDEFS t t₁) = inj₂ (λ { n () })
is-INL PURE = inj₂ (λ { n () })
is-INL (TERM t) = inj₂ (λ { n () })
is-INL (ENC t) = inj₂ (λ { n () })
is-INL (UNIV x) = inj₂ (λ { n () })
is-INL (LIFT t) = inj₂ (λ { n () })
is-INL (LOWER t) = inj₂ (λ { n () })
is-INL (SHRINK t) = inj₂ (λ { n () })


is-INR : (t : Term) → (Σ Term (λ u → t ≡ INR u)) ⊎ ((u : Term) → ¬ t ≡ INR u)
is-INR (VAR x) = inj₂ (λ { n () })
is-INR NAT = inj₂ (λ { n () })
is-INR QNAT = inj₂ (λ { n () })
is-INR TNAT = inj₂ (λ { n () })
is-INR (LT t t₁) = inj₂ (λ { n () })
is-INR (QLT t t₁) = inj₂ (λ { n () })
is-INR (NUM x) = inj₂ (λ { n () })
is-INR (IFLT t t₁ t₂ t₃) = inj₂ (λ { n () })
is-INR (IFEQ t t₁ t₂ t₃) = inj₂ (λ { n () })
is-INR (SUC t) = inj₂ (λ { n () })
is-INR (PI t t₁) = inj₂ (λ { n () })
is-INR (LAMBDA t) = inj₂ (λ { n () })
is-INR (APPLY t t₁) = inj₂ (λ { n () })
is-INR (FIX t) = inj₂ (λ { n () })
is-INR (LET t t₁) = inj₂ (λ { n () })
is-INR (WT t t₁) = inj₂ (λ { n () })
is-INR (SUP t t₁) = inj₂ (λ { n () })
--is-INR (DSUP t t₁) = inj₂ (λ { n () })
is-INR (WREC t t₁) = inj₂ (λ { n () })
is-INR (MT t t₁) = inj₂ (λ { n () })
--is-INR (MSUP t t₁) = inj₂ (λ { n () })
--is-INR (DMSUP t t₁) = inj₂ (λ { n () })
is-INR (SUM t t₁) = inj₂ (λ { n () })
is-INR (PAIR t t₁) = inj₂ (λ { n () })
is-INR (SPREAD t t₁) = inj₂ (λ { n () })
is-INR (SET t t₁) = inj₂ (λ { n () })
is-INR (ISECT t t₁) = inj₂ (λ { n () })
is-INR (TUNION t t₁) = inj₂ (λ { n () })
is-INR (UNION t t₁) = inj₂ (λ { n () })
is-INR (QTUNION t t₁) = inj₂ (λ { n () })
is-INR (INL t) = inj₂ (λ { n () })
is-INR (INR t) = inj₁ (t , refl)
is-INR (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-INR (EQ t t₁ t₂) = inj₂ (λ { n () })
is-INR (EQB t t₁ t₂ t₃) = inj₂ (λ { n () })
is-INR AX = inj₂ (λ { n () })
is-INR FREE = inj₂ (λ { n () })
is-INR (MSEQ x) = inj₂ (λ { n () })
is-INR (MAPP s t) = inj₂ (λ { n () })
is-INR (CS x) = inj₂ (λ { n () })
is-INR (NAME x) = inj₂ (λ { n () })
is-INR (FRESH t) = inj₂ (λ { n () })
is-INR (LOAD t) = inj₂ (λ { n () })
is-INR (CHOOSE t t₁) = inj₂ (λ { n () })
--is-INR (IFC0 t t₁ t₂) = inj₂ (λ { n () })
is-INR (TSQUASH t) = inj₂ (λ { n () })
is-INR (TTRUNC t) = inj₂ (λ { n () })
is-INR (TCONST t) = inj₂ (λ { n () })
is-INR (SUBSING t) = inj₂ (λ { n () })
is-INR (DUM t) = inj₂ (λ { n () })
is-INR (FFDEFS t t₁) = inj₂ (λ { n () })
is-INR PURE = inj₂ (λ { n () })
is-INR (TERM t) = inj₂ (λ { n () })
is-INR (ENC t) = inj₂ (λ { n () })
is-INR (UNIV x) = inj₂ (λ { n () })
is-INR (LIFT t) = inj₂ (λ { n () })
is-INR (LOWER t) = inj₂ (λ { n () })
is-INR (SHRINK t) = inj₂ (λ { n () })




data ∼vals : Term → Term → Set where
  ∼vals-NAT     : ∼vals NAT NAT
  ∼vals-QNAT    : ∼vals QNAT QNAT
  ∼vals-TNAT    : ∼vals TNAT TNAT
  ∼vals-LT      : {a b c d : Term} → ∼vals (LT a b) (LT c d)
  ∼vals-QLT     : {a b c d : Term} → ∼vals (QLT a b) (QLT c d)
  ∼vals-NUM     : {n : ℕ} → ∼vals (NUM n) (NUM n)
  ∼vals-PI      : {a b c d : Term} → ∼vals (PI a b) (PI c d)
  ∼vals-LAMBDA  : {a b : Term} → ∼vals (LAMBDA a) (LAMBDA b)
  ∼vals-SUM     : {a b c d : Term} → ∼vals (SUM a b) (SUM c d)
  ∼vals-PAIR    : {a b c d : Term} → ∼vals (PAIR a b) (PAIR c d)
  ∼vals-SET     : {a b c d : Term} → ∼vals (SET a b) (SET c d)
  ∼vals-ISECT   : {a b c d : Term} → ∼vals (ISECT a b) (ISECT c d)
  ∼vals-TUNION  : {a b c d : Term} → ∼vals (TUNION a b) (TUNION c d)
  ∼vals-UNION   : {a b c d : Term} → ∼vals (UNION a b) (UNION c d)
  ∼vals-QTUNION : {a b c d : Term} → ∼vals (QTUNION a b) (QTUNION c d)
  ∼vals-INL     : {a b : Term} → ∼vals (INL a) (INL b)
  ∼vals-INR     : {a b : Term} → ∼vals (INR a) (INR b)
  ∼vals-EQ      : {a b c d e f : Term} → ∼vals (EQ a b c) (EQ d e f)
  ∼vals-EQB      : {a b c d e f g h : Term} → ∼vals (EQB a b c d) (EQB e f g h)
  ∼vals-AX      : ∼vals AX AX
  ∼vals-FREE    : ∼vals FREE FREE
  ∼vals-MSEQ    : {s : 𝕊} → ∼vals (MSEQ s) (MSEQ s)
  ∼vals-CS      : {n : Name} → ∼vals (CS n) (CS n)
  ∼vals-NAME    : {n : Name} → ∼vals (NAME n) (NAME n)
  ∼vals-TSQUASH : {a b : Term} → ∼vals (TSQUASH a) (TSQUASH b)
  ∼vals-TTRUNC  : {a b : Term} → ∼vals (TTRUNC a) (TTRUNC b)
  ∼vals-TCONST  : {a b : Term} → ∼vals (TCONST a) (TCONST b)
  ∼vals-SUBSING : {a b : Term} → ∼vals (SUBSING a) (SUBSING b)
  ∼vals-DUM     : {a b : Term} → ∼vals (DUM a) (DUM b)
  ∼vals-FFDEFS  : {a b c d : Term} → ∼vals (FFDEFS a b) (FFDEFS c d)
  ∼vals-PURE    : ∼vals PURE PURE
  ∼vals-TERM    : {a b : Term} → ∼vals (TERM a) (TERM b)
  ∼vals-UNIV    : {n : ℕ} → ∼vals (UNIV n) (UNIV n)
  ∼vals-LIFT    : {a b : Term} → ∼vals (LIFT a) (LIFT b)
  ∼vals-LOWER   : {a b : Term} → ∼vals (LOWER a) (LOWER b)
  ∼vals-SHRINK  : {a b : Term} → ∼vals (SHRINK a) (SHRINK b)


∼vals-sym : {a b : Term} → ∼vals a b → ∼vals b a
∼vals-sym {.NAT} {.NAT} ∼vals-NAT = ∼vals-NAT
∼vals-sym {.QNAT} {.QNAT} ∼vals-QNAT = ∼vals-QNAT
∼vals-sym {.TNAT} {.TNAT} ∼vals-TNAT = ∼vals-TNAT
∼vals-sym {.(LT _ _)} {.(LT _ _)} ∼vals-LT = ∼vals-LT
∼vals-sym {.(QLT _ _)} {.(QLT _ _)} ∼vals-QLT = ∼vals-QLT
∼vals-sym {.(NUM _)} {.(NUM _)} ∼vals-NUM = ∼vals-NUM
∼vals-sym {.(PI _ _)} {.(PI _ _)} ∼vals-PI = ∼vals-PI
∼vals-sym {.(LAMBDA _)} {.(LAMBDA _)} ∼vals-LAMBDA = ∼vals-LAMBDA
∼vals-sym {.(SUM _ _)} {.(SUM _ _)} ∼vals-SUM = ∼vals-SUM
∼vals-sym {.(PAIR _ _)} {.(PAIR _ _)} ∼vals-PAIR = ∼vals-PAIR
∼vals-sym {.(SET _ _)} {.(SET _ _)} ∼vals-SET = ∼vals-SET
∼vals-sym {.(ISECT _ _)} {.(ISECT _ _)} ∼vals-ISECT = ∼vals-ISECT
∼vals-sym {.(TUNION _ _)} {.(TUNION _ _)} ∼vals-TUNION = ∼vals-TUNION
∼vals-sym {.(UNION _ _)} {.(UNION _ _)} ∼vals-UNION = ∼vals-UNION
∼vals-sym {.(QTUNION _ _)} {.(QTUNION _ _)} ∼vals-QTUNION = ∼vals-QTUNION
∼vals-sym {.(INL _)} {.(INL _)} ∼vals-INL = ∼vals-INL
∼vals-sym {.(INR _)} {.(INR _)} ∼vals-INR = ∼vals-INR
∼vals-sym {.(EQ _ _ _)} {.(EQ _ _ _)} ∼vals-EQ = ∼vals-EQ
∼vals-sym {.(EQB _ _ _ _)} {.(EQB _ _ _ _)} ∼vals-EQB = ∼vals-EQB
∼vals-sym {.AX} {.AX} ∼vals-AX = ∼vals-AX
∼vals-sym {.FREE} {.FREE} ∼vals-FREE = ∼vals-FREE
∼vals-sym {.(MSEQ _)} {.(MSEQ _)} ∼vals-MSEQ = ∼vals-MSEQ
∼vals-sym {.(CS _)} {.(CS _)} ∼vals-CS = ∼vals-CS
∼vals-sym {.(NAME _)} {.(NAME _)} ∼vals-NAME = ∼vals-NAME
∼vals-sym {.(TSQUASH _)} {.(TSQUASH _)} ∼vals-TSQUASH = ∼vals-TSQUASH
∼vals-sym {.(TTRUNC _)} {.(TTRUNC _)} ∼vals-TTRUNC = ∼vals-TTRUNC
∼vals-sym {.(TCONST _)} {.(TCONST _)} ∼vals-TCONST = ∼vals-TCONST
∼vals-sym {.(SUBSING _)} {.(SUBSING _)} ∼vals-SUBSING = ∼vals-SUBSING
∼vals-sym {.(DUM _)} {.(DUM _)} ∼vals-DUM = ∼vals-DUM
∼vals-sym {.(FFDEFS _ _)} {.(FFDEFS _ _)} ∼vals-FFDEFS = ∼vals-FFDEFS
∼vals-sym {.(PURE)} {.(PURE)} ∼vals-PURE = ∼vals-PURE
∼vals-sym {.(TERM _)} {.(TERM _)} ∼vals-TERM = ∼vals-TERM
∼vals-sym {.(UNIV _)} {.(UNIV _)} ∼vals-UNIV = ∼vals-UNIV
∼vals-sym {.(LIFT _)} {.(LIFT _)} ∼vals-LIFT = ∼vals-LIFT
∼vals-sym {.(LOWER _)} {.(LOWER _)} ∼vals-LOWER = ∼vals-LOWER
∼vals-sym {.(SHRINK _)} {.(SHRINK _)} ∼vals-SHRINK = ∼vals-SHRINK


∼vals→isValue₁ : {a b : Term} → ∼vals a b → isValue a
∼vals→isValue₁ {NAT} {b} isv = tt
∼vals→isValue₁ {QNAT} {b} isv = tt
∼vals→isValue₁ {TNAT} {b} isv = tt
∼vals→isValue₁ {LT a a₁} {b} isv = tt
∼vals→isValue₁ {QLT a a₁} {b} isv = tt
∼vals→isValue₁ {NUM x} {b} isv = tt
∼vals→isValue₁ {PI a a₁} {b} isv = tt
∼vals→isValue₁ {LAMBDA a} {b} isv = tt
∼vals→isValue₁ {SUM a a₁} {b} isv = tt
∼vals→isValue₁ {PAIR a a₁} {b} isv = tt
∼vals→isValue₁ {SET a a₁} {b} isv = tt
∼vals→isValue₁ {ISECT a a₁} {b} isv = tt
∼vals→isValue₁ {TUNION a a₁} {b} isv = tt
∼vals→isValue₁ {UNION a a₁} {b} isv = tt
∼vals→isValue₁ {QTUNION a a₁} {b} isv = tt
∼vals→isValue₁ {INL a} {b} isv = tt
∼vals→isValue₁ {INR a} {b} isv = tt
∼vals→isValue₁ {EQ a a₁ a₂} {b} isv = tt
∼vals→isValue₁ {EQB a a₁ a₂ a₃} {b} isv = tt
∼vals→isValue₁ {AX} {b} isv = tt
∼vals→isValue₁ {FREE} {b} isv = tt
∼vals→isValue₁ {MSEQ x} {b} isv = tt
∼vals→isValue₁ {CS x} {b} isv = tt
∼vals→isValue₁ {NAME x} {b} isv = tt
∼vals→isValue₁ {TSQUASH a} {b} isv = tt
∼vals→isValue₁ {TTRUNC a} {b} isv = tt
∼vals→isValue₁ {TCONST a} {b} isv = tt
∼vals→isValue₁ {SUBSING a} {b} isv = tt
∼vals→isValue₁ {DUM a} {b} isv = tt
∼vals→isValue₁ {FFDEFS a a₁} {b} isv = tt
∼vals→isValue₁ {PURE} {b} isv = tt
∼vals→isValue₁ {TERM a} {b} isv = tt
∼vals→isValue₁ {UNIV x} {b} isv = tt
∼vals→isValue₁ {LIFT a} {b} isv = tt
∼vals→isValue₁ {LOWER a} {b} isv = tt
∼vals→isValue₁ {SHRINK a} {b} isv = tt


∼vals→isValue₂ : {a b : Term} → ∼vals a b → isValue b
∼vals→isValue₂ {a} {VAR x} ()
∼vals→isValue₂ {a} {NAT} isv = tt
∼vals→isValue₂ {a} {QNAT} isv = tt
∼vals→isValue₂ {a} {TNAT} isv = tt
∼vals→isValue₂ {a} {LT b b₁} isv = tt
∼vals→isValue₂ {a} {QLT b b₁} isv = tt
∼vals→isValue₂ {a} {NUM x} isv = tt
∼vals→isValue₂ {a} {IFLT b b₁ b₂ b₃} ()
∼vals→isValue₂ {a} {IFEQ b b₁ b₂ b₃} ()
∼vals→isValue₂ {a} {SUC b} ()
∼vals→isValue₂ {a} {PI b b₁} isv = tt
∼vals→isValue₂ {a} {LAMBDA b} isv = tt
∼vals→isValue₂ {a} {APPLY b b₁} ()
∼vals→isValue₂ {a} {FIX b} ()
∼vals→isValue₂ {a} {LET b b₁} ()
∼vals→isValue₂ {a} {WT b b₁} isv = tt
∼vals→isValue₂ {a} {SUP b b₁} isv = tt
--∼vals→isValue₂ {a} {DSUP b b₁} ()
∼vals→isValue₂ {a} {WREC b b₁} ()
∼vals→isValue₂ {a} {MT b b₁} isv = tt
--∼vals→isValue₂ {a} {MSUP b b₁} isv = tt
--∼vals→isValue₂ {a} {DMSUP b b₁} ()
∼vals→isValue₂ {a} {SUM b b₁} isv = tt
∼vals→isValue₂ {a} {PAIR b b₁} isv = tt
∼vals→isValue₂ {a} {SPREAD b b₁} ()
∼vals→isValue₂ {a} {SET b b₁} isv = tt
∼vals→isValue₂ {a} {ISECT b b₁} isv = tt
∼vals→isValue₂ {a} {TUNION b b₁} isv = tt
∼vals→isValue₂ {a} {UNION b b₁} isv = tt
∼vals→isValue₂ {a} {QTUNION b b₁} isv = tt
∼vals→isValue₂ {a} {INL b} isv = tt
∼vals→isValue₂ {a} {INR b} isv = tt
∼vals→isValue₂ {a} {DECIDE b b₁ b₂} ()
∼vals→isValue₂ {a} {EQ b b₁ b₂} isv = tt
∼vals→isValue₂ {a} {EQB b b₁ b₂ b₃} isv = tt
∼vals→isValue₂ {a} {AX} isv = tt
∼vals→isValue₂ {a} {FREE} isv = tt
∼vals→isValue₂ {a} {MSEQ x} isv = tt
∼vals→isValue₂ {a} {CS x} isv = tt
∼vals→isValue₂ {a} {NAME x} isv = tt
∼vals→isValue₂ {a} {TSQUASH b} isv = tt
∼vals→isValue₂ {a} {TTRUNC b} isv = tt
∼vals→isValue₂ {a} {TCONST b} isv = tt
∼vals→isValue₂ {a} {SUBSING b} isv = tt
∼vals→isValue₂ {a} {DUM b} isv = tt
∼vals→isValue₂ {a} {FFDEFS b b₁} isv = tt
∼vals→isValue₂ {a} {PURE} isv = tt
∼vals→isValue₂ {a} {TERM b} isv = tt
∼vals→isValue₂ {a} {UNIV x} isv = tt
∼vals→isValue₂ {a} {LIFT b} isv = tt
∼vals→isValue₂ {a} {LOWER b} isv = tt
∼vals→isValue₂ {a} {SHRINK b} isv = tt


#∼vals : CTerm → CTerm → Set
#∼vals a b = ∼vals ⌜ a ⌝ ⌜ b ⌝


#isValue : CTerm -> Set
#isValue t = isValue ⌜ t ⌝


¬read : Term → Bool
¬read (VAR x) = true
¬read NAT = true
¬read QNAT = true
¬read TNAT = true
¬read (LT t t₁) = ¬read t ∧ ¬read t₁
¬read (QLT t t₁) = ¬read t ∧ ¬read t₁
¬read (NUM x) = true
¬read (IFLT t t₁ t₂ t₃) = ¬read t ∧ ¬read t₁ ∧ ¬read t₂ ∧ ¬read t₃
¬read (IFEQ t t₁ t₂ t₃) = ¬read t ∧ ¬read t₁ ∧ ¬read t₂ ∧ ¬read t₃
¬read (SUC t) = ¬read t
¬read (PI t t₁) = ¬read t ∧ ¬read t₁
¬read (LAMBDA t) = ¬read t
¬read (APPLY t t₁) = ¬read t ∧ ¬read t₁
¬read (FIX t) = ¬read t
¬read (LET t t₁) = ¬read t ∧ ¬read t₁
¬read (WT t t₁) = ¬read t ∧ ¬read t₁
¬read (SUP t t₁) = ¬read t ∧ ¬read t₁
--¬read (DSUP t t₁) = ¬read t ∧ ¬read t₁
¬read (WREC t t₁) = ¬read t ∧ ¬read t₁
¬read (MT t t₁) = ¬read t ∧ ¬read t₁
--¬read (MSUP t t₁) = ¬read t ∧ ¬read t₁
--¬read (DMSUP t t₁) = ¬read t ∧ ¬read t₁
¬read (SUM t t₁) = ¬read t ∧ ¬read t₁
¬read (PAIR t t₁) = ¬read t ∧ ¬read t₁
¬read (SPREAD t t₁) = ¬read t ∧ ¬read t₁
¬read (SET t t₁) = ¬read t ∧ ¬read t₁
¬read (ISECT t t₁) = ¬read t ∧ ¬read t₁
¬read (TUNION t t₁) = ¬read t ∧ ¬read t₁
¬read (UNION t t₁) = ¬read t ∧ ¬read t₁
¬read (QTUNION t t₁) = ¬read t ∧ ¬read t₁
¬read (INL t) = ¬read t
¬read (INR t) = ¬read t
¬read (DECIDE t t₁ t₂) = ¬read t ∧ ¬read t₁ ∧ ¬read t₂
¬read (EQ t t₁ t₂) = ¬read t ∧ ¬read t₁ ∧ ¬read t₂
¬read (EQB t t₁ t₂ t₃) = ¬read t ∧ ¬read t₁ ∧ ¬read t₂ ∧ ¬read t₃
¬read AX = true
¬read FREE = true
¬read (MSEQ x) = true
¬read (MAPP s t) = ¬read t
¬read (CS x) = false -- ONLY FALSE
¬read (NAME x) = true
¬read (FRESH t) = ¬read t
¬read (LOAD t) = ¬read t
¬read (CHOOSE t t₁) = ¬read t ∧ ¬read t₁
--¬read (IFC0 t t₁ t₂) = ¬read t ∧ ¬read t₁ ∧ ¬read t₂
¬read (TSQUASH t) = ¬read t
¬read (TTRUNC t) = ¬read t
¬read (TCONST t) = ¬read t
¬read (SUBSING t) = ¬read t
¬read (DUM t) = ¬read t
¬read (FFDEFS t t₁) = ¬read t ∧ ¬read t₁
¬read PURE = true
¬read (TERM t) = ¬read t
¬read (ENC t) = ¬read t
¬read (UNIV x) = true
¬read (LIFT t) = ¬read t
¬read (LOWER t) = ¬read t
¬read (SHRINK t) = ¬read t


#¬read : CTerm → Bool
#¬read t = ¬read ⌜ t ⌝


¬Read : Term → Set
¬Read t = ¬read t ≡ true


#¬Read : CTerm → Set
#¬Read t = #¬read t ≡ true


¬names : Term → Bool
¬names (VAR x) = true
¬names NAT = true
¬names QNAT = true
¬names TNAT = true
¬names (LT t t₁) = ¬names t ∧ ¬names t₁
¬names (QLT t t₁) = ¬names t ∧ ¬names t₁
¬names (NUM x) = true
¬names (IFLT t t₁ t₂ t₃) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂ ∧ ¬names t₃
¬names (IFEQ t t₁ t₂ t₃) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂ ∧ ¬names t₃
¬names (SUC t) = ¬names t
¬names (PI t t₁) = ¬names t ∧ ¬names t₁
¬names (LAMBDA t) = ¬names t
¬names (APPLY t t₁) = ¬names t ∧ ¬names t₁
¬names (FIX t) = ¬names t
¬names (LET t t₁) = ¬names t ∧ ¬names t₁
¬names (WT t t₁) = ¬names t ∧ ¬names t₁
¬names (SUP t t₁) = ¬names t ∧ ¬names t₁
--¬names (DSUP t t₁) = ¬names t ∧ ¬names t₁
¬names (WREC t t₁) = ¬names t ∧ ¬names t₁
¬names (MT t t₁) = ¬names t ∧ ¬names t₁
--¬names (MSUP t t₁) = ¬names t ∧ ¬names t₁
--¬names (DMSUP t t₁) = ¬names t ∧ ¬names t₁
¬names (SUM t t₁) = ¬names t ∧ ¬names t₁
¬names (PAIR t t₁) = ¬names t ∧ ¬names t₁
¬names (SPREAD t t₁) = ¬names t ∧ ¬names t₁
¬names (SET t t₁) = ¬names t ∧ ¬names t₁
¬names (ISECT t t₁) = ¬names t ∧ ¬names t₁
¬names (TUNION t t₁) = ¬names t ∧ ¬names t₁
¬names (UNION t t₁) = ¬names t ∧ ¬names t₁
¬names (QTUNION t t₁) = ¬names t ∧ ¬names t₁
¬names (INL t) = ¬names t
¬names (INR t) = ¬names t
¬names (DECIDE t t₁ t₂) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂
¬names (EQ t t₁ t₂) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂
¬names (EQB t t₁ t₂ t₃) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂ ∧ ¬names t₃
¬names AX = true
¬names FREE = true
¬names (MSEQ x) = true
¬names (MAPP s t) = ¬names t
¬names (CS x) = false -- FALSE
¬names (NAME x) = false -- FALSE
¬names (FRESH t) = false -- FALSE
¬names (LOAD t) = false -- FALSE
¬names (CHOOSE t t₁) = ¬names t ∧ ¬names t₁
--¬names (IFC0 t t₁ t₂) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂
¬names (TSQUASH t) = ¬names t
¬names (TTRUNC t) = ¬names t
¬names (TCONST t) = ¬names t
¬names (SUBSING t) = ¬names t
¬names (DUM t) = ¬names t
¬names (FFDEFS t t₁) = ¬names t ∧ ¬names t₁
¬names PURE = true
¬names (TERM t) = ¬names t
¬names (ENC t) = ¬names t
¬names (UNIV x) = true
¬names (LIFT t) = ¬names t
¬names (LOWER t) = ¬names t
¬names (SHRINK t) = ¬names t


#¬names : CTerm → Bool
#¬names t = ¬names ⌜ t ⌝


¬Names : Term → Set
¬Names t = ¬names t ≡ true


#¬Names : CTerm → Set
#¬Names t = #¬names t ≡ true


#names : CTerm → List Name
#names t = names ⌜ t ⌝


noseq : Term → Bool
noseq (VAR x) = true
noseq NAT = true
noseq QNAT = true
noseq TNAT = true
noseq (LT t t₁) = noseq t ∧ noseq t₁
noseq (QLT t t₁) = noseq t ∧ noseq t₁
noseq (NUM x) = true
noseq (IFLT t t₁ t₂ t₃) = noseq t ∧ noseq t₁ ∧ noseq t₂ ∧ noseq t₃
noseq (IFEQ t t₁ t₂ t₃) = noseq t ∧ noseq t₁ ∧ noseq t₂ ∧ noseq t₃
noseq (SUC t) = noseq t
noseq (PI t t₁) = noseq t ∧ noseq t₁
noseq (LAMBDA t) = noseq t
noseq (APPLY t t₁) = noseq t ∧ noseq t₁
noseq (FIX t) = noseq t
noseq (LET t t₁) = noseq t ∧ noseq t₁
noseq (WT t t₁) = noseq t ∧ noseq t₁
noseq (SUP t t₁) = noseq t ∧ noseq t₁
noseq (WREC t t₁) = noseq t ∧ noseq t₁
noseq (MT t t₁) = noseq t ∧ noseq t₁
noseq (SUM t t₁) = noseq t ∧ noseq t₁
noseq (PAIR t t₁) = noseq t ∧ noseq t₁
noseq (SPREAD t t₁) = noseq t ∧ noseq t₁
noseq (SET t t₁) = noseq t ∧ noseq t₁
noseq (TUNION t t₁) = noseq t ∧ noseq t₁
noseq (ISECT t t₁) = noseq t ∧ noseq t₁
noseq (UNION t t₁) = noseq t ∧ noseq t₁
noseq (QTUNION t t₁) = noseq t ∧ noseq t₁
noseq (INL t) = noseq t
noseq (INR t) = noseq t
noseq (DECIDE t t₁ t₂) = noseq t ∧ noseq t₁ ∧ noseq t₂
noseq (EQ t t₁ t₂) = noseq t ∧ noseq t₁ ∧ noseq t₂
noseq (EQB t t₁ t₂ t₃) = noseq t ∧ noseq t₁ ∧ noseq t₂ ∧ noseq t₃
noseq AX = true
noseq FREE = true
noseq (CS x) = true
noseq (NAME x) = true
noseq (FRESH t) = noseq t
noseq (CHOOSE t t₁) = noseq t ∧ noseq t₁
noseq (LOAD t) = noseq t
noseq (MSEQ x) = false
noseq (MAPP x t) = false
noseq (TSQUASH t) = noseq t
noseq (TTRUNC t) = noseq t
noseq (TCONST t) = noseq t
noseq (SUBSING t) = noseq t
noseq (DUM t) = noseq t
noseq (FFDEFS t t₁) = noseq t ∧ noseq t₁
noseq PURE = true
noseq (TERM t) = noseq t
noseq (ENC t) = noseq t
noseq (UNIV x) = true
noseq (LIFT t) = noseq t
noseq (LOWER t) = noseq t
noseq (SHRINK t) = noseq t

\end{code}
