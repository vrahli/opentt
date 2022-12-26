\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --auto-inline #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
--open import choiceBar


module barCont {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
               (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
               (X : ChoiceExt W C)
               (N : NewChoice {L} W C K G)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
               (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import terms7(W)(C)(K)(G)(X)(N)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)



-- inspired by: https://arxiv.org/pdf/1608.03814.pdf
-- bib to be clarified


-- generic element with the index of as 1st arg.
-- - name of the reference (r)
-- - list as length (k) + function (f)
-- - index (i)
-- We assume that the reference is set to true and set it to false if we don't have enough information in the sequence
genericI : Name → Term → Term → Term → Term
genericI r k f i =
  SEQ choose (APPLY f i)
  where
    choose : Term
    choose = IFLT i k AX (CHOOSE (NAME r) BFALSE)


generic : Name → Term → Term -- λ (l,f) i → genericI l f i
generic r xs = LAMBDA (genericI r (FST xs) (SND xs) (VAR 0))


FunBar : Term
FunBar = FUN (FUN NAT NAT) NAT


UNIT : Term
UNIT = TRUE


VOID : Term
VOID = FALSE


IndBarB : Term
IndBarB = UNION NAT UNIT


IndBarC : Term
IndBarC = DECIDE (VAR 0) VOID NAT


IndBar : Term
IndBar = WT IndBarB IndBarC


CoIndBar : Term
CoIndBar = MT IndBarB IndBarC


ETA : Term → Term
ETA n = LAMBDA (SUP (INL n) AX)


DIGAMMA : Term → Term
DIGAMMA f = LAMBDA (SUP (INR AX) f)


barThesis : Term
barThesis = FUN FunBar IndBar


-- appends a new value
APPEND : Term → Term → Term
APPEND l x = PAIR (SUC k) (LAMBDA (IFLT (VAR 0) k (APPLY f (VAR 0)) x))
  where
    k : Term
    k = FST l

    f : Term
    f = SND l


-- empty list
EMPTY : Term
EMPTY = PAIR (NUM 0) (LAMBDA AX)



loopF : Name → Term → Term → Term → Term
loopF r bar R xs =
  SEQ (CHOOSE (NAME r) BTRUE) -- we start by assuming that we have enough information
      (LET (APPLY bar (generic r xs))
           (ITE (CS r)
                (ETA (VAR 0))
                (DIGAMMA (LAMBDA (APPLY (shiftUp 0 (shiftUp 0 R)) (APPEND (shiftUp 0 (shiftUp 0 xs)) (VAR 0)))))))


loop : Name →  Term → Term
loop r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  FIX (LAMBDA (LAMBDA (loopF r bar (VAR 1) (VAR 0))))


tabI : Term → Term
tabI bar = FRESH (APPLY (loop 0 bar) EMPTY)


tab : Term
tab = LAMBDA (tabI (VAR 0))


-- A path is a function that provides the B's to follow in a member of a W(A,B) of M(A,B) type
-- An infinite path (only inj₁'s) cannot be a path of a W type because eventually (sub a B) will be false
-- and '∈Type i w (sub0 a B) b' will be false
path : (i : ℕ) (w : 𝕎·) → CTerm → CTerm0 → Set(lsuc L)
path i w A B = (n : ℕ) → Σ CTerm (λ a → Σ CTerm (λ b → ∈Type i w A a × ∈Type i w (sub0 a B) b)) ⊎ ⊤


is-inj₁ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B) → Set
is-inj₁ {I} {J} {A} {B} (inj₁ x) = ⊤
is-inj₁ {I} {J} {A} {B} (inj₂ x) = ⊥

is-inj₂ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B) → Set
is-inj₂ {I} {J} {A} {B} (inj₁ x) = ⊥
is-inj₂ {I} {J} {A} {B} (inj₂ x) = ⊤


-- A path is infinite if it is made out of inj₁'s
isInfPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B) → Set
isInfPath {i} {w} {A} {B} p = (n : ℕ) → is-inj₁ (p n)


isFinPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B) → Set
isFinPath {i} {w} {A} {B} p = Σ ℕ (λ n → is-inj₂ (p n))


is-inj₁→¬is-inj₂ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B)
                    → is-inj₁ u
                    → ¬ is-inj₂ u
is-inj₁→¬is-inj₂ {I} {J} {A} {B} (inj₁ x) i j = j
is-inj₁→¬is-inj₂ {I} {J} {A} {B} (inj₂ x) i j = i


isFinPath→¬isInfPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B)
                        → isFinPath {i} {w} {A} {B} p
                        → ¬ isInfPath {i} {w} {A} {B} p
isFinPath→¬isInfPath {i} {w} {A} {B} p (n , fin) inf = is-inj₁→¬is-inj₂ (p n) (inf n) fin


shiftPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B) → path i w A B
shiftPath {i} {w} {A} {B} p k = p (suc k)


-- Defines what it means for a path to be correct w.r.t. a W or M type -- up to n (with fuel)
correctPathN : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (t : CTerm) (p : path i w A B) (n : ℕ) → Set
correctPathN {i} {w} {A} {B} t p 0 = ⊤
correctPathN {i} {w} {A} {B} t p (suc n) with p 0
... | inj₁ (a , b , ia , ib) =
  Σ CTerm (λ x → Σ CTerm (λ f →
    t #⇓ #SUP x f at w -- For W types
    × x ≡ a
    × correctPathN {i} {w} {A} {B} (#APPLY f b) (shiftPath {i} {w} {A} {B} p) n))
... | inj₂ _ = ⊤


-- A path is correct, if it is so for all ℕs
correctPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (t : CTerm) (p : path i w A B) → Set
correctPath {i} {w} {A} {B} t p = (n : ℕ) → correctPathN {i} {w} {A} {B} t p n


record branch (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
record branch eqa eqb w t1 t2 where
  coinductive
  field
    branchC : Σ CTerm (λ a1 → Σ CTerm (λ f1 → Σ CTerm (λ b1 → Σ CTerm (λ a2 → Σ CTerm (λ f2 → Σ CTerm (λ b2 → Σ (eqa a1 a2) (λ e →
               t1 #⇓ (#SUP a1 f1) at w
               × t2 #⇓ (#SUP a2 f2) at w
               × eqb a1 a2 e b1 b2
               × branch eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))))))))


-- ¬ weq tells us which b's to follow
m2mb : (w : 𝕎·) (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t u : CTerm)
         → meq eqa eqb w t u
         → ¬ weq eqa eqb w t u
         → branch eqa eqb w t u
branch.branchC (m2mb w eqa eqb t u m nw) with meq.meqC m
... | (a1 , f1 , a2 , f2 , e , c1 , c2 , q) =
  a1 , f1 , fst k , a2 , f2 , fst (snd k) , e , c1 , c2 , fst (snd (snd k)) ,
  m2mb w eqa eqb (#APPLY f1 (fst k)) (#APPLY f2 (fst (snd k))) (q (fst k) (fst (snd k)) (fst (snd (snd k)))) (snd (snd (snd k)))
  where
    nj : ¬ ((b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))
    nj h = nw (weq.weqC a1 f1 a2 f2 e c1 c2 h)

    k : Σ CTerm (λ b1 → Σ CTerm (λ b2 → Σ (eqb a1 a2 e b1 b2) (λ eb → ¬ weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))))
    k with EM {Σ CTerm (λ b1 → Σ CTerm (λ b2 → Σ (eqb a1 a2 e b1 b2) (λ eb → ¬ weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))))}
    ... | yes p = p
    ... | no p = ⊥-elim (nj j)
      where
        j : (b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2)
        j b1 b2 eb with EM {weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2)}
        ... | yes pp = pp
        ... | no pp = ⊥-elim (p (b1 , b2 , eb , pp))



-- Build a path from branch
mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
          → branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
          → path i w A B
mb2path i w A B t u m 0 with branch.branchC m
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = inj₁ (a1 , b1 , equalInType-refl ea , equalInType-refl eb)
mb2path i w A B t u m (suc n) with branch.branchC m
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n


correctN-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                   (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
                   (n : ℕ)
                   → correctPathN {i} {w} {A} {B} t (mb2path i w A B t u b) n
correctN-mb2path i w A B t u b 0 = tt
correctN-mb2path i w A B t u b (suc n) with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) =
  a1 , f1 , c1 , refl , correctN-mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n


correct-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                  (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
                  → correctPath {i} {w} {A} {B} t (mb2path i w A B t u b)
correct-mb2path i w A B t u b n = correctN-mb2path i w A B t u b n


inf-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
              (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
              → isInfPath {i} {w} {A} {B} (mb2path i w A B t u b)
inf-mb2path i w A B t u b 0 with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = tt
inf-mb2path i w A B t u b (suc n) with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) with inf-mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n
... |    k with mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n
... |       inj₁ x = tt
... |       inj₂ x = k


-- Classically, we can derive a weq from an meq as follows
m2wa : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
      → ((p : path i w A B) → correctPath {i} {w} {A} {B} t p → isFinPath {i} {w} {A} {B} p)
      → meq (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
      → weq (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
m2wa i w A B t u cond h with EM {weq (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u}
... | yes p = p
... | no q = ⊥-elim (isFinPath→¬isInfPath {i} {w} {A} {B} p fin inf)
  where
    b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
    b = m2mb w (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) t u h q

    p : path i w A B
    p = mb2path i w A B t u b

    c : correctPath {i} {w} {A} {B} t p
    c = correctN-mb2path i w A B t u b

    inf : isInfPath {i} {w} {A} {B} p
    inf = inf-mb2path i w A B t u b

    fin : isFinPath {i} {w} {A} {B} p
    fin = cond p c


-- Can we prove?
m2w : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t : CTerm)
      → ∀𝕎 w (λ w' _ → isType i w' A)
      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
      → ((p : path i w A B) → correctPath {i} {w} {A} {B} t p → isFinPath {i} {w} {A} {B} p)
      → ∈Type i w (#MT A B) t
      → ∈Type i w (#WT A B) t
m2w i w A B t eqta eqtb cond h = →equalInType-W i w A B t t eqta eqtb (Mod.∀𝕎-□Func M aw q)
  where
    q : □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    q = equalInType-M→ i w A B t t h

    aw : ∀𝕎 w (λ w' e' → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t
                       → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    aw w' e' z = {!!} -- ues m2wa but the worlds don't match


-- First prove that loop belongs to CoIndBar
--coSem : (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
--          → ∈Type i w #FunBar F
--          → ∈Type i w #CoIndBar (#loop r F)
--coSem w  ?


--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?


\end{code}
