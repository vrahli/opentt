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
open import terms8(W)(C)(K)(G)(X)(N)

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
generic r xs = LAMBDA (genericI r (FST (shiftUp 0 xs)) (SND (shiftUp 0 xs)) (VAR 0))


FunBar : Term
FunBar = BAIRE→NAT


#FunBar : CTerm
#FunBar = #BAIRE→NAT


IndBarB : Term
IndBarB = UNION NAT UNIT


#UNIT : CTerm
#UNIT = ct UNIT refl


#IndBarB : CTerm
#IndBarB = #UNION #NAT #UNIT


IndBarC : Term
IndBarC = DECIDE (VAR 0) VOID NAT


#IndBarC : CTerm0
#IndBarC = #[0]DECIDE #[0]VAR #[1]VOID #[1]NAT


IndBar : Term
IndBar = WT IndBarB IndBarC


#IndBar : CTerm
#IndBar = #WT #IndBarB #IndBarC


CoIndBar : Term
CoIndBar = MT IndBarB IndBarC


#CoIndBar : CTerm
#CoIndBar = #MT #IndBarB #IndBarC


ETA : Term → Term
ETA n = LAMBDA (SUP (INL (shiftUp 0 n)) AX)


DIGAMMA : Term → Term
DIGAMMA f = LAMBDA (SUP (INR AX) (shiftUp 0 f))


barThesis : Term
barThesis = FUN FunBar IndBar


-- appends a new value
APPEND : Term → Term → Term
APPEND l x = PAIR (SUC k) (LAMBDA (IFLT (VAR 0) (shiftUp 0 k) (APPLY (shiftUp 0 f) (VAR 0)) (shiftUp 0 x)))
  where
    k : Term
    k = FST l

    f : Term
    f = SND l


-- empty list
EMPTY : Term
EMPTY = PAIR (NUM 0) (LAMBDA AX)


PROD : Term → Term → Term
PROD a b = SUM a (shiftUp 0 b)


#PROD : CTerm → CTerm → CTerm
#PROD a b = ct (PROD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # PROD ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | #shiftUp 0 b | lowerVars-fvars-CTerm≡[] b = refl


LIST : Term → Term
LIST A = PROD NAT BAIRE


#LIST : CTerm → CTerm
#LIST A = #PROD #NAT #BAIRE


loopF : Name → Term → Term → Term → Term
loopF r bar R xs =
  SEQ (CHOOSE (NAME r) BTRUE) -- we start by assuming that we have enough information
      (LET (APPLY bar (generic r xs))
           (ITE (CS r)
                (ETA (VAR 0))
                (DIGAMMA (LAMBDA (APPLY (shiftUp 0 (shiftUp 0 R)) (APPEND (shiftUp 0 (shiftUp 0 xs)) (VAR 0)))))))


loopL : Name →  Term → Term
loopL r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  LAMBDA (LAMBDA (loopF r bar (VAR 1) (VAR 0)))


loop : Name →  Term → Term
loop r bar = FIX (loopL r bar)


#generic : Name → CTerm → CTerm -- λ (l,f) i → genericI l f i
#generic r xs =
  #LAMBDA (#[0]SEQ (#[0]IFLT #[0]VAR (#[0]FST (#[0]shiftUp0 xs)) #[0]AX (#[0]CHOOSE (#[0]NAME r) #[0]BFALSE))
                   (#[0]APPLY (#[0]SND (#[0]shiftUp0 xs)) #[0]VAR))


#[1]generic : Name → CTerm1 → CTerm1 -- λ (l,f) i → genericI l f i
#[1]generic r xs =
  #[1]LAMBDA (#[2]SEQ (#[2]IFLT #[2]VAR0 (#[2]FST (#[2]shiftUp0 xs)) #[2]AX (#[2]CHOOSE (#[2]NAME r) #[2]BFALSE))
                      (#[2]APPLY (#[2]SND (#[2]shiftUp0 xs)) #[2]VAR0))


#[0]ETA : CTerm0 → CTerm0
#[0]ETA n = #[0]LAMBDA (#[1]SUP (#[1]INL (#[1]shiftUp0 n)) #[1]AX)


#[2]ETA : CTerm2 → CTerm2
#[2]ETA n = #[2]LAMBDA (#[3]SUP (#[3]INL (#[3]shiftUp0 n)) #[3]AX)


#[0]DIGAMMA : CTerm0 → CTerm0
#[0]DIGAMMA f = #[0]LAMBDA (#[1]SUP (#[1]INR #[1]AX) (#[1]shiftUp0 f))


#[2]DIGAMMA : CTerm2 → CTerm2
#[2]DIGAMMA f = #[2]LAMBDA (#[3]SUP (#[3]INR #[3]AX) (#[3]shiftUp0 f))


#[1]APPEND : CTerm1 → CTerm1 → CTerm1
#[1]APPEND l x =
  #[1]PAIR (#[1]SUC (#[1]FST l))
           (#[1]LAMBDA (#[2]IFLT #[2]VAR0
                                 (#[2]shiftUp0 (#[1]FST l))
                                 (#[2]APPLY (#[2]shiftUp0 (#[1]SND l)) #[2]VAR0)
                                 (#[2]shiftUp0 x)))


#[3]APPEND : CTerm3 → CTerm3 → CTerm3
#[3]APPEND l x =
  #[3]PAIR (#[3]SUC (#[3]FST l))
           (#[3]LAMBDA (#[4]IFLT #[4]VAR0
                                 (#[4]shiftUp0 (#[3]FST l))
                                 (#[4]APPLY (#[4]shiftUp0 (#[3]SND l)) #[4]VAR0)
                                 (#[4]shiftUp0 x)))


#loopF : Name →  CTerm → CTerm → CTerm → CTerm
#loopF r bar R l =
  -- 0 is the argument (the list), and 1 is the recursive call
  #SEQ (#CHOOSE (#NAME r) #BTRUE) F
  where
    F : CTerm
    F = #LET (#APPLY bar (#generic r l))
             (#[0]ITE (#[0]CS r)
                      (#[0]ETA #[0]VAR)
                      (#[0]DIGAMMA (#[0]LAMBDA (#[1]APPLY (#[1]shiftUp0 (#[0]shiftUp0 R))
                                                          (#[1]APPEND (#[1]shiftUp0 (#[0]shiftUp0 l)) #[1]VAR0)))))


#loop : Name →  CTerm → CTerm
#loop r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  #FIX (#LAMBDA (#[0]LAMBDA (#[1]SEQ (#[1]CHOOSE (#[1]NAME r) #[1]BTRUE) F)))
  where
    F : CTerm1
    F = #[1]LET (#[1]APPLY ⌞ bar ⌟ (#[1]generic r #[1]VAR0))
                (#[2]ITE (#[2]CS r)
                         (#[2]ETA #[2]VAR0)
                         (#[2]DIGAMMA (#[2]LAMBDA (#[3]APPLY #[3]VAR3 (#[3]APPEND #[3]VAR2 #[3]VAR0)))))


-- sanity checking
⌜#[1]generic⌝≡ : (r : Name) (xs : CTerm1) → ⌜ #[1]generic r xs ⌝ ≡ generic r ⌜ xs ⌝
⌜#[1]generic⌝≡ r xs = refl


-- sanity checking
⌜#loop⌝≡ : (r : Name) (F : CTerm) → ⌜ #loop r F ⌝ ≡ loop r ⌜ F ⌝
⌜#loop⌝≡ r F = refl


-- sanity checking
⌜#loopF⌝≡ : (r : Name) (F R l : CTerm) → ⌜ #loopF r F R l ⌝ ≡ loopF r ⌜ F ⌝ ⌜ R ⌝ ⌜ l ⌝
⌜#loopF⌝≡ r F R l = refl


tabI : Term → Term
tabI bar = FRESH (APPLY (loop 0 bar) EMPTY)


tab : Term
tab = LAMBDA (tabI (VAR 0))


-- A path is a function that provides the B's to follow in a member of a W(A,B) of M(A,B) type
-- An infinite path (only inj₁'s) cannot be a path of a W type because eventually (sub a B) will be false
-- and '∈Type i w (sub0 a B) b' will be false
path : (i : ℕ) → CTerm → CTerm0 → Set(lsuc L)
path i A B = (n : ℕ) → Σ 𝕎· (λ w → Σ CTerm (λ a → Σ CTerm (λ b → ∈Type i w A a × ∈Type i w (sub0 a B) b))) ⊎ ⊤


is-inj₁ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B) → Set
is-inj₁ {I} {J} {A} {B} (inj₁ x) = ⊤
is-inj₁ {I} {J} {A} {B} (inj₂ x) = ⊥

is-inj₂ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B) → Set
is-inj₂ {I} {J} {A} {B} (inj₁ x) = ⊥
is-inj₂ {I} {J} {A} {B} (inj₂ x) = ⊤


-- A path is infinite if it is made out of inj₁'s
isInfPath : {i : ℕ} {A : CTerm} {B : CTerm0} (p : path i A B) → Set
isInfPath {i} {A} {B} p = (n : ℕ) → is-inj₁ (p n)


isFinPath : {i : ℕ} {A : CTerm} {B : CTerm0} (p : path i A B) → Set
isFinPath {i} {A} {B} p = Σ ℕ (λ n → is-inj₂ (p n))


is-inj₁→¬is-inj₂ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B)
                    → is-inj₁ u
                    → ¬ is-inj₂ u
is-inj₁→¬is-inj₂ {I} {J} {A} {B} (inj₁ x) i j = j
is-inj₁→¬is-inj₂ {I} {J} {A} {B} (inj₂ x) i j = i


isFinPath→¬isInfPath : {i : ℕ} {A : CTerm} {B : CTerm0} (p : path i A B)
                        → isFinPath {i} {A} {B} p
                        → ¬ isInfPath {i} {A} {B} p
isFinPath→¬isInfPath {i} {A} {B} p (n , fin) inf = is-inj₁→¬is-inj₂ (p n) (inf n) fin


shiftPath : {i : ℕ} {A : CTerm} {B : CTerm0} (p : path i A B) → path i A B
shiftPath {i} {A} {B} p k = p (suc k)


-- Defines what it means for a path to be correct w.r.t. a W or M type -- up to n (with fuel)
correctPathN : {i : ℕ} {A : CTerm} {B : CTerm0} (t : CTerm) (p : path i A B) (n : ℕ) → Set(lsuc L)
correctPathN {i} {A} {B} t p 0 = Lift (lsuc L) ⊤
correctPathN {i} {A} {B} t p (suc n) with p 0
... | inj₁ (w , a , b , ia , ib) =
  Σ CTerm (λ x → Σ CTerm (λ f →
    t #⇛ #SUP x f at w -- For W types
    × x ≡ a
    × correctPathN {i} {A} {B} (#APPLY f b) (shiftPath {i} {A} {B} p) n))
... | inj₂ _ = Lift (lsuc L) ⊤


-- A path is correct, if it is so for all ℕs
correctPath : {i : ℕ} {A : CTerm} {B : CTerm0} (t : CTerm) (p : path i A B) → Set(lsuc L)
correctPath {i} {A} {B} t p = (n : ℕ) → correctPathN {i} {A} {B} t p n


record branch (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
record branch eqa eqb w t1 t2 where
  coinductive
  field
    branchC : Σ CTerm (λ a1 → Σ CTerm (λ f1 → Σ CTerm (λ b1 → Σ CTerm (λ a2 → Σ CTerm (λ f2 → Σ CTerm (λ b2 → Σ (eqa a1 a2) (λ e →
               t1 #⇛ (#SUP a1 f1) at w
               × t2 #⇛ (#SUP a2 f2) at w
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
          → path i A B
mb2path i w A B t u m 0 with branch.branchC m
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = inj₁ (w , a1 , b1 , equalInType-refl ea , equalInType-refl eb)
mb2path i w A B t u m (suc n) with branch.branchC m
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n


correctN-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                   (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
                   (n : ℕ)
                   → correctPathN {i} {A} {B} t (mb2path i w A B t u b) n
correctN-mb2path i w A B t u b 0 = lift tt
correctN-mb2path i w A B t u b (suc n) with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) =
  a1 , f1 , c1 , refl , correctN-mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n


correct-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                  (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
                  → correctPath {i} {A} {B} t (mb2path i w A B t u b)
correct-mb2path i w A B t u b n = correctN-mb2path i w A B t u b n


inf-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
              (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
              → isInfPath {i} {A} {B} (mb2path i w A B t u b)
inf-mb2path i w A B t u b 0 with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = tt
inf-mb2path i w A B t u b (suc n) with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) with inf-mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n
... |    k with mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n
... |       inj₁ x = tt
... |       inj₂ x = k


data compatMW (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm)
              : meq eqa eqb w t1 t2 → weq eqa eqb w t1 t2 → Set
data compatMW eqa eqb w t1 t2 where
  compMWC : (a1 f1 a2 f2 : CTerm) (ea : eqa a1 a2)
            (c1 : t1 #⇛ (#SUP a1 f1) at w)
            (c2 : t2 #⇛ (#SUP a2 f2) at w)
            (eb : (b1 b2 : CTerm) → eqb a1 a2 ea b1 b2 → weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))
            (m : meq eqa eqb w t1 t2) -- get rid of that + induction
            → compatMW eqa eqb w t1 t2 m {--(meq.meqC (a1 , f1 , a2 , f2 , ? , c1 , c2 , ?))--} (weq.weqC a1 f1 a2 f2 ea c1 c2 eb)


-- Classically, we can derive a weq from an meq as follows
m2wa : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
      → ((p : path i A B) → correctPath {i} {A} {B} t p → isFinPath {i} {A} {B} p)
      → meq (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
      → weq (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
m2wa i w A B t u cond h with EM {weq (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u}
... | yes p = p
... | no q = ⊥-elim (isFinPath→¬isInfPath {i} {A} {B} p fin inf)
  where
    b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
    b = m2mb w (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) t u h q

    p : path i A B
    p = mb2path i w A B t u b

    c : correctPath {i} {A} {B} t p
    c = correctN-mb2path i w A B t u b

    inf : isInfPath {i} {A} {B} p
    inf = inf-mb2path i w A B t u b

    fin : isFinPath {i} {A} {B} p
    fin = cond p c


m2w : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t : CTerm)
      → ∀𝕎 w (λ w' _ → isType i w' A)
      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
      → ((p : path i A B) → correctPath {i} {A} {B} t p → isFinPath {i} {A} {B} p)
      → ∈Type i w (#MT A B) t
      → ∈Type i w (#WT A B) t
m2w i w A B t eqta eqtb cond h =
  →equalInType-W i w A B t t eqta eqtb (Mod.∀𝕎-□Func M aw q)
  where
    q : □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    q = equalInType-M→ i w A B t t h

    aw : ∀𝕎 w (λ w' e' → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t
                       → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    aw w' e' z = m2wa i w' A B t t cond z


{--→equalInType-meq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm)
                    → t1 #⇓ (#SUP a1 f1) at w
                    → t2 #⇓ (#SUP a2 f2) at w
                    → meq eqa eqb w t1 t2
--}


sub-LAMBDA-loopF≡ : (r : Name) (F : Term) (cF : # F)
                    → sub (loop r F) (LAMBDA (loopF r F (VAR 1) (VAR 0)))
                       ≡ LAMBDA (loopF r F (loop r F) (VAR 0))
sub-LAMBDA-loopF≡ r F cF
  rewrite #subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 (loop r F)))) (shiftUp 0 F) (→#shiftUp 0 {F} cF)
        | #shiftUp 0 (ct F cF)
        | #shiftDown 2 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 5 (ct F cF)
        | #shiftUp 7 (ct F cF)
        | #shiftDown 9 (ct F cF)
  = refl


sub-loopF≡ : (r : Name) (F l : Term) (cF : # F) (cl : # l)
             → sub l (loopF r F (loop r F) (VAR 0))
                ≡ loopF r F (loop r F) l
sub-loopF≡ r F l cF cl
  rewrite #subv 1 (shiftUp 0 (shiftUp 0 l)) (shiftUp 0 F) (→#shiftUp 0 {F} cF)
        | #shiftUp 0 (ct F cF)
        | #shiftDown 1 (ct F cF)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 1 (ct l cl)
        | #shiftUp 2 (ct l cl)
        | #shiftDown 2 (ct l cl)
        | #shiftDown 3 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftDown 5 (ct l cl)
        | #shiftDown 6 (ct l cl)
        | #shiftUp 3 (ct l cl)
        | #shiftUp 5 (ct l cl)
        | #shiftUp 4 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 5 (ct F cF)
        | #shiftUp 7 (ct F cF)
        | #subv 8 l F cF
        | #shiftDown 8 (ct F cF)
  = refl


APPLY-loop⇓! : (r : Name) (F l : Term) (w : 𝕎·) (cF : # F) (cl : # l)
                → APPLY (loop r F) l ⇓! loopF r F (loop r F) l at w
APPLY-loop⇓! r F l w cF cl =
  step-⇓-from-to-trans
    {w} {w} {w}
    {APPLY (loop r F) l}
    {APPLY (LAMBDA (loopF r F (loop r F) (VAR 0))) l}
    {loopF r F (loop r F) l}
    c1
    (step-⇓-from-to-trans
      {w} {w} {w}
      {APPLY (LAMBDA (loopF r F (loop r F) (VAR 0))) l}
      {loopF r F (loop r F) l}
      {loopF r F (loop r F) l}
      c2
      (0 , refl))
  where
    c1 : ret (APPLY (sub (loop r F) (LAMBDA (loopF r F (VAR 1) (VAR 0)))) l) w
         ≡ just (APPLY (LAMBDA (loopF r F (loop r F) (VAR 0))) l , w)
    c1 rewrite sub-LAMBDA-loopF≡ r F cF = refl

    c2 : ret (sub l (loopF r F (loop r F) (VAR 0))) w
         ≡ just (loopF r F (loop r F) l , w)
    c2 rewrite sub-loopF≡ r F l cF cl = refl


-- sanity checking
⌜APPLY-loop⌝≡ : (r : Name) (F l : CTerm) → ⌜ #APPLY (#loop r F) l ⌝ ≡ APPLY (loop r ⌜ F ⌝) ⌜ l ⌝
⌜APPLY-loop⌝≡ r F l = refl


-- sanity checking
⌜loopF-loop⌝≡ : (r : Name) (F l : CTerm) → ⌜ #loopF r F (#loop r F) l ⌝ ≡ loopF r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝
⌜loopF-loop⌝≡ r F l rewrite ⌜#loop⌝≡ r F = refl


#APPLY-#loop#⇛! : (r : Name) (F l : CTerm) (w : 𝕎·)
                   → #APPLY (#loop r F) l #⇛! #loopF r F (#loop r F) l at w
#APPLY-#loop#⇛! r F l w w1 e1 = lift c
  where
    c : ⌜ #APPLY (#loop r F) l ⌝ ⇓! ⌜ #loopF r F (#loop r F) l ⌝ at w1
    c  = APPLY-loop⇓! r ⌜ F ⌝ ⌜ l ⌝ w1 (CTerm.closed F) (CTerm.closed l)


-- First prove that loop belongs to CoIndBar
coSemM : (i : ℕ) (w : 𝕎·) (r : Name) (F l : CTerm)
         → ∈Type i w #FunBar F
         → ∈Type i w (#LIST #BOOL) l
         → meq (equalInType i w #IndBarB)
                (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                w (#APPLY (#loop r F) l) (#APPLY (#loop r F) l)
meq.meqC (coSemM i w r F l j k) = {!!}


-- First prove that loop belongs to CoIndBar
coSem : (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → ∈Type i w #FunBar F
        → ∈Type i w #CoIndBar (#loop r F)
coSem i w r F j =
  →equalInType-M
    i w #IndBarB #IndBarC (#loop r F) (#loop r F)
      {!!}
      {!!}
      (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → meq (equalInType i w' #IndBarB)
                              (λ a b eqa → equalInType i w' (sub0 a #IndBarC))
                              w' (#loop r F) (#loop r F))
    aw w1 e1 = m
      where
        m : meq (equalInType i w1 #IndBarB)
                (λ a b eqa → equalInType i w1 (sub0 a #IndBarC))
                w1 (#loop r F) (#loop r F)
        m = {!!}


--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?


{--

Plan:

(1) Prove by coinduction that if (F ∈ FunBar) then (loop r F ∈ CoIndBar) which does not require to proving termination
    - see coSem, which will use coSemM
(2) We now have an inhabitant (t ∈ CoIndBar). Using classical logic, either t's paths are all finite,
    or it has an inifite path.
(3) If all its paths are finite then we get that (t ∈ IndBar)
    - see m2w
(4) If it has an inifite path:
    - That path corresponds to an (α ∈ Baire).
    - Given (F ∈ FunBar), by continuity let n by F's modulus of continuity w.r.t. α.
    - So, it must be that F(generic r α|n) returns r:=BTRUE and so loop returns ETA, and the path cannot be infinite
          (where α|n is the initial segment of α of length n)

 --}

\end{code}
