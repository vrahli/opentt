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
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)



-- inspired by: https://arxiv.org/pdf/1608.03814.pdf
-- bib to be clarified



-- MOVE to computation
#⇓-trans₁ : {w w' : 𝕎·} {a b c : CTerm} → a #⇓ b from w to w' → b #⇓ c at w' → a #⇓ c at w
#⇓-trans₁ {w} {w'} {a} {b} {c} c₁ c₂ = ⇓-trans₁ {w} {w'} {⌜ a ⌝} {⌜ b ⌝} {⌜ c ⌝} c₁ c₂


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
    choose = IFLT i k AX (set⊥ r)


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


-- IndBarC uses NAT! because if DIGAMMAs are functions from NAT, then to prove that (loop ∈ coW -- see coSemM)
-- we need to jump to the 𝕎s at wihch the NATs are actual numbers, and we don't have members of the coW at the
-- current 𝕎
IndBarC : Term
IndBarC = DECIDE (VAR 0) VOID NAT!


#IndBarC : CTerm0
#IndBarC = #[0]DECIDE #[0]VAR #[1]VOID #[1]NAT!


IndBar : Term
IndBar = WT IndBarB IndBarC


#IndBar : CTerm
#IndBar = #WT #IndBarB #IndBarC


CoIndBar : Term
CoIndBar = MT IndBarB IndBarC


#CoIndBar : CTerm
#CoIndBar = #MT #IndBarB #IndBarC


ETA : Term → Term
ETA n = SUP (INL n) AX


DIGAMMA : Term → Term
DIGAMMA f = SUP (INR AX) f


barThesis : Term
barThesis = FUN FunBar IndBar


-- Recursive call used in DIGAMMA
loopR : Term → Term → Term
loopR R xs = LAMBDA (LET (VAR 0) (APPLY (shiftUp 0 (shiftUp 0 R)) (APPEND (shiftUp 0 (shiftUp 0 xs)) (VAR 0))))


-- loopA's body
loopI : Name → Term → Term → Term → Term
loopI r R xs i =
  ITE (get0 r)
      (ETA i)
      (DIGAMMA (loopR R xs))


loopB : Name → Term → Term → Term → Term
loopB r a R xs = LET a (loopI r (shiftUp 0 R) (shiftUp 0 xs) (VAR 0))


loopA : Name → Term → Term → Term → Term
loopA r bar R xs = loopB r (APPLY bar (generic r xs)) R xs


loopF : Name → Term → Term → Term → Term
loopF r bar R xs =
  SEQ (set⊤ r) -- we start by assuming that we have enough information
      (loopA r bar R xs)


loopL : Name →  Term → Term
loopL r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  LAMBDA (LAMBDA (loopF r bar (VAR 1) (VAR 0)))


loop : Name →  Term → Term
loop r bar = FIX (loopL r bar)


#genericI : Name → CTerm → CTerm → CTerm → CTerm
#genericI r k f i = #SEQ (#IFLT i k #AX (#set⊥ r)) (#APPLY f i)


#generic : Name → CTerm → CTerm -- λ (l,f) i → genericI l f i
#generic r xs =
  #LAMBDA (#[0]SEQ (#[0]IFLT #[0]VAR (#[0]FST (#[0]shiftUp0 xs)) #[0]AX (#[0]set⊥ r))
                   (#[0]APPLY (#[0]SND (#[0]shiftUp0 xs)) #[0]VAR))


#[1]generic : Name → CTerm1 → CTerm1 -- λ (l,f) i → genericI l f i
#[1]generic r xs =
  #[1]LAMBDA (#[2]SEQ (#[2]IFLT #[2]VAR0 (#[2]FST (#[2]shiftUp0 xs)) #[2]AX (#[2]set⊥ r))
                      (#[2]APPLY (#[2]SND (#[2]shiftUp0 xs)) #[2]VAR0))


#ETA : CTerm → CTerm
#ETA n = #SUP (#INL n) #AX


#[0]ETA : CTerm0 → CTerm0
#[0]ETA n = #[0]SUP (#[0]INL n) #[0]AX


#[2]ETA : CTerm2 → CTerm2
#[2]ETA n = #[2]SUP (#[2]INL n) #[2]AX


#DIGAMMA : CTerm → CTerm
#DIGAMMA f = #SUP (#INR #AX) f


#[0]DIGAMMA : CTerm0 → CTerm0
#[0]DIGAMMA f = #[0]SUP (#[0]INR #[0]AX) f


#[2]DIGAMMA : CTerm2 → CTerm2
#[2]DIGAMMA f = #[2]SUP (#[2]INR #[2]AX) f


#APPENDf : CTerm → CTerm → CTerm → CTerm
#APPENDf n f x =
  #LAMBDA (#[0]IFLT #[0]VAR
                    (#[0]shiftUp0 n)
                    (#[0]APPLY (#[0]shiftUp0 f) #[0]VAR)
                    (#[0]shiftUp0 x))


#APPEND : CTerm → CTerm → CTerm
#APPEND l x =
  #SPREAD l (#[1]PAIR (#[1]SUC #[1]VAR0)
                      (#[1]LAMBDA (#[2]IFLT #[2]VAR0
                                            #[2]VAR1
                                            (#[2]APPLY #[2]VAR2 #[2]VAR0)
                                            (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 x))))))


#[0]APPEND : CTerm0 → CTerm0 → CTerm0
#[0]APPEND l x =
  #[0]SPREAD l (#[2]PAIR (#[2]SUC #[2]VAR0)
                         (#[2]LAMBDA (#[3]IFLT #[3]VAR0
                                               #[3]VAR1
                                               (#[3]APPLY #[3]VAR2 #[3]VAR0)
                                               (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 x))))))


#[1]APPEND : CTerm1 → CTerm1 → CTerm1
#[1]APPEND l x =
  #[1]SPREAD l (#[3]PAIR (#[3]SUC #[3]VAR0)
                         (#[3]LAMBDA (#[4]IFLT #[4]VAR0
                                               #[4]VAR1
                                               (#[4]APPLY #[4]VAR2 #[4]VAR0)
                                               (#[4]shiftUp0 (#[3]shiftUp0 (#[2]shiftUp0 x))))))


#[2]APPEND : CTerm2 → CTerm2 → CTerm2
#[2]APPEND l x =
  #[2]SPREAD l (#[4]PAIR (#[4]SUC #[4]VAR0)
                         (#[4]LAMBDA (#[5]IFLT #[5]VAR0
                                               #[5]VAR1
                                               (#[5]APPLY #[5]VAR2 #[5]VAR0)
                                               (#[5]shiftUp0 (#[4]shiftUp0 (#[3]shiftUp0 x))))))


#[3]APPEND : CTerm3 → CTerm3 → CTerm3
#[3]APPEND l x =
  #[3]SPREAD l (#[5]PAIR (#[5]SUC #[5]VAR0)
                         (#[5]LAMBDA (#[6]IFLT #[6]VAR0
                                               #[6]VAR1
                                               (#[6]APPLY #[6]VAR2 #[6]VAR0)
                                               (#[6]shiftUp0 (#[5]shiftUp0 (#[4]shiftUp0 x))))))


#[4]APPEND : CTerm4 → CTerm4 → CTerm4
#[4]APPEND l x =
  #[4]SPREAD l (#[6]PAIR (#[6]SUC #[6]VAR0)
                         (#[6]LAMBDA (#[7]IFLT #[7]VAR0
                                               #[7]VAR1
                                               (#[7]APPLY #[7]VAR2 #[7]VAR0)
                                               (#[7]shiftUp0 (#[6]shiftUp0 (#[5]shiftUp0 x))))))


#loopRL : CTerm → CTerm → CTerm → CTerm
#loopRL a R l = #LET a (#[0]APPLY (#[0]shiftUp0 R) (#[0]APPEND (#[0]shiftUp0 l) #[0]VAR))


-- Recursive call used in DIGAMMA
#loopR : CTerm → CTerm → CTerm
#loopR R l = #LAMBDA (#[0]LET #[0]VAR (#[1]APPLY (#[1]shiftUp0 (#[0]shiftUp0 R)) (#[1]APPEND (#[1]shiftUp0 (#[0]shiftUp0 l)) #[1]VAR0)))


-- This is loopA's body
#loopI : Name →  CTerm → CTerm → ℕ → CTerm
#loopI r R l i =
  #ITE (#get0 r)
       (#ETA (#NUM i))
       (#DIGAMMA (#loopR R l))


#loopA : Name →  CTerm → CTerm → CTerm → CTerm
#loopA r bar R l =
  #LET (#APPLY bar (#generic r l))
       (#[0]ITE (#[0]get0 r)
                (#[0]ETA #[0]VAR)
                (#[0]DIGAMMA (#[0]LAMBDA (#[1]LET #[1]VAR0 (#[2]APPLY (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 R)))
                                                                      (#[2]APPEND (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 l))) #[2]VAR0))))))


#loopF : Name →  CTerm → CTerm → CTerm → CTerm
#loopF r bar R l =
  -- 0 is the argument (the list), and 1 is the recursive call
  #SEQ (#set⊤ r) (#loopA r bar R l)


#loop : Name →  CTerm → CTerm
#loop r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  #FIX (#LAMBDA (#[0]LAMBDA (#[1]SEQ (#[1]set⊤ r) F)))
  where
    F : CTerm1
    F = #[1]LET (#[1]APPLY ⌞ bar ⌟ (#[1]generic r #[1]VAR0))
                (#[2]ITE (#[2]get0 r)
                         (#[2]ETA #[2]VAR0)
                         (#[2]DIGAMMA (#[2]LAMBDA (#[3]LET #[3]VAR0 (#[4]APPLY #[4]VAR4 (#[4]APPEND #[4]VAR3 #[4]VAR0))))))


-- sanity checking
⌜#[1]generic⌝≡ : (r : Name) (xs : CTerm1) → ⌜ #[1]generic r xs ⌝ ≡ generic r ⌜ xs ⌝
⌜#[1]generic⌝≡ r xs = refl


-- sanity checking
⌜#loop⌝≡ : (r : Name) (F : CTerm) → ⌜ #loop r F ⌝ ≡ loop r ⌜ F ⌝
⌜#loop⌝≡ r F = refl


-- sanity checking
⌜#loopI⌝≡ : (r : Name) (R l : CTerm) (i : ℕ) → ⌜ #loopI r R l i ⌝ ≡ loopI r ⌜ R ⌝ ⌜ l ⌝ (NUM i)
⌜#loopI⌝≡ r R l i = refl


-- sanity checking
⌜#loopA⌝≡ : (r : Name) (F R l : CTerm) → ⌜ #loopA r F R l ⌝ ≡ loopA r ⌜ F ⌝ ⌜ R ⌝ ⌜ l ⌝
⌜#loopA⌝≡ r F R l = refl


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
    t #⇓ {--#⇛--} #SUP x f at w -- For W types
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
               t1 #⇓ {--#⇛--} (#SUP a1 f1) at w
               × t2 #⇓ {--#⇛--} (#SUP a2 f2) at w
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


{--
data compatMW (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm)
              : meq eqa eqb w t1 t2 → weq eqa eqb w t1 t2 → Set
data compatMW eqa eqb w t1 t2 where
  compMWC : (a1 f1 a2 f2 : CTerm) (ea : eqa a1 a2)
            (c1 : t1 #⇛ (#SUP a1 f1) at w)
            (c2 : t2 #⇛ (#SUP a2 f2) at w)
            (eb : (b1 b2 : CTerm) → eqb a1 a2 ea b1 b2 → weq eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))
            (m : meq eqa eqb w t1 t2) -- get rid of that + induction
            → compatMW eqa eqb w t1 t2 m {--(meq.meqC (a1 , f1 , a2 , f2 , ? , c1 , c2 , ?))--} (weq.weqC a1 f1 a2 f2 ea c1 c2 eb)
--}


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
        | #shiftUp 6 (ct F cF)
        | #shiftUp 7 (ct F cF)
        | #shiftDown 8 (ct F cF)
        | #shiftDown 9 (ct F cF)
  = refl


sub-loopF≡ : (r : Name) (F l : Term) (cF : # F) (cl : # l)
             → sub l (loopF r F (loop r F) (VAR 0))
                ≡ loopF r F (loop r F) l
sub-loopF≡ r F l cF cl
  rewrite #shiftUp 0 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 5 (ct F cF)
        | #shiftUp 7 (ct F cF)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftDown 2 (ct l cl)
        | #shiftDown 3 (ct l cl)
        | #shiftDown 5 (ct l cl)
        | #shiftDown 6 (ct l cl)
        | #subv 1 l F cF
        | #subv 8 l F cF
        | #shiftDown 1 (ct F cF)
        | #shiftDown 8 (ct F cF)
        | #shiftUp 1 (ct l cl)
        | #shiftUp 2 (ct l cl)
        | #shiftUp 3 (ct l cl)
        | #shiftUp 4 (ct l cl)
        | #shiftUp 5 (ct l cl)
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


#APPLY-#loop#⇓1 : (r : Name) (F l : CTerm) (w : 𝕎·)
                   → #APPLY (#loop r F) l #⇓! #loopF r F (#loop r F) l at w
#APPLY-#loop#⇓1 r F l w = APPLY-loop⇓! r ⌜ F ⌝ ⌜ l ⌝ w (CTerm.closed F) (CTerm.closed l)


#APPLY-#loop#⇓2 : (r : Name) (F l : CTerm) (w : 𝕎·)
                  → #APPLY (#loop r F) l #⇓ #loopA r F (#loop r F) l from w to (chooseT r w BTRUE)
#APPLY-#loop#⇓2 r F l w =
  ⇓-trans₂ {w} {w} {chooseT r w BTRUE}
           {APPLY (loop r ⌜ F ⌝) ⌜ l ⌝}
           {loopF r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
           {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
           (#APPLY-#loop#⇓1 r F l w)
           (step-⇓-from-to-trans {w} {chooseT r w BTRUE} {chooseT r w BTRUE}
                                 {loopF r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
                                 {SEQ AX (loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝)}
                                 {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
                                 refl
                                 (SEQ-AX⇓₁from-to {chooseT r w BTRUE} {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
                                                  (CTerm.closed (#loopA r F (#loop r F) l))))


sub-genericI : (r : Name) (i a b : Term) (ci : # i) (ca : # a) (cb : # b)
               → sub i (genericI r a b (VAR 0)) ≡ genericI r a b i
sub-genericI r i a b ci ca cb
  rewrite #shiftUp 0 (ct i ci)
        | #shiftDown 0 (ct i ci)
        | #subv 0 i a ca
        | #shiftDown 0 (ct a ca)
        | #shiftUp 0 (ct i ci)
        | #shiftDown 1 (ct i ci)
        | #shiftUp 0 (ct b cb)
        | #subv 1 i b cb
        | #shiftDown 1 (ct b cb) =
  ≡LET (≡IFLT refl refl refl refl) (≡APPLY refl refl)


#FST-shiftUp : (a : CTerm) → # FST (shiftUp 0 ⌜ a ⌝)
#FST-shiftUp a rewrite →#shiftUp 0 {⌜ a ⌝} (CTerm.closed a) = refl


#SND-shiftUp : (a : CTerm) → # SND (shiftUp 0 ⌜ a ⌝)
#SND-shiftUp a rewrite →#shiftUp 0 {⌜ a ⌝} (CTerm.closed a) = refl


#APPLY-#generic⇓ : (r : Name) (l i : CTerm) (w : 𝕎·)
                   → #APPLY (#generic r l) i #⇓ #genericI r (#FST l) (#SND l) i from w to w
#APPLY-#generic⇓ r l i w =
  step-⇓-from-to-trans
    {w} {w} {w}
    {APPLY (generic r ⌜ l ⌝) ⌜ i ⌝}
    {genericI r (FST ⌜ l ⌝) (SND ⌜ l ⌝) ⌜ i ⌝}
    {genericI r (FST ⌜ l ⌝) (SND ⌜ l ⌝) ⌜ i ⌝}
    c
    (0 , refl)
  where
    c : ret (sub ⌜ i ⌝ (genericI r (FST (shiftUp 0 ⌜ l ⌝)) (SND (shiftUp 0 ⌜ l ⌝)) (VAR 0))) w
        ≡ just (genericI r (FST ⌜ l ⌝) (SND ⌜ l ⌝) ⌜ i ⌝ , w)
    c rewrite sub-genericI r ⌜ i ⌝ (FST (shiftUp 0 ⌜ l ⌝)) (SND (shiftUp 0 ⌜ l ⌝)) (CTerm.closed i) (#FST-shiftUp l) (#SND-shiftUp l)
            | #shiftUp 0 l
            | #shiftUp 0 l = refl


𝕎< : (n m : ℕ) (w w1 w2 : 𝕎·) → 𝕎·
𝕎< n m w w1 w2 with n <? m
... | yes p = w1
... | no p = w2


u𝕎 : (r : Name) (n m : ℕ) (w : 𝕎·) → 𝕎·
u𝕎 r n m w = 𝕎< n m w w (chooseT r w BFALSE)


IFLT⇓𝕎< : {w w1 w2 : 𝕎·} {a b c : Term} {n m : ℕ}
           → a ⇓ c from w to w1
           → b ⇓ c from w to w2
           → IFLT (NUM n) (NUM m) a b ⇓ c from w to 𝕎< n m w w1 w2
IFLT⇓𝕎< {w} {w1} {w2} {a} {b} {c} {n} {m} c1 c2 with n <? m
... | yes p = step-⇓-from-to-trans {w} {w} {w1} {IFLT (NUM n) (NUM m) a b} {a} {c} comp c1
  where
    comp : step (IFLT (NUM n) (NUM m) a b) w ≡ just (a , w)
    comp with n <? m
    ... | yes q = refl
    ... | no q = ⊥-elim (q p)
... | no p = step-⇓-from-to-trans {w} {w} {w2} {IFLT (NUM n) (NUM m) a b} {b} {c} comp c2
  where
    comp : step (IFLT (NUM n) (NUM m) a b) w ≡ just (b , w)
    comp with n <? m
    ... | yes q = ⊥-elim (p q)
    ... | no q = refl


IFLT-NUM-AX-CHOOSE⇓ : (r : Name) (n m : ℕ) (w : 𝕎·)
                      → IFLT (NUM n) (NUM m) AX (set⊥ r) ⇓ AX from w to u𝕎 r n m w
IFLT-NUM-AX-CHOOSE⇓ r n m w =
  IFLT⇓𝕎<
    {w} {w} {chooseT r w BFALSE} {AX} {set⊥ r} {AX} {n} {m}
    (⇓!-refl AX w)
    (1 , refl)


#APPLY-#generic⇓2 : (r : Name) (l i k f : CTerm) (w : 𝕎·) (m n : ℕ)
                    → l #⇛ #PAIR k f at w
                    → i #⇛ #NUM n at w
                    → k #⇛ #NUM m at w
                    → Σ 𝕎· (λ w' → #APPLY (#generic r l) i #⇓ #APPLY (#SND l) i from w to u𝕎 r n m w')
#APPLY-#generic⇓2 r l i k f w m n cl ci ck =
  fst c2 , ⇓-trans₂
             {w} {w} {u𝕎 r n m (fst c2)}
             {APPLY (generic r ⌜ l ⌝) ⌜ i ⌝}
             {genericI r (FST ⌜ l ⌝) (SND ⌜ l ⌝) ⌜ i ⌝}
             {APPLY (SND ⌜ l ⌝) ⌜ i ⌝}
             (#APPLY-#generic⇓ r l i w)
             (⇓-trans₂
                {w} {u𝕎 r n m (proj₁ c2)} {u𝕎 r n m (proj₁ c2)}
                {genericI r (FST ⌜ l ⌝) (SND ⌜ l ⌝) ⌜ i ⌝}
                {SEQ AX (APPLY (SND ⌜ l ⌝) ⌜ i ⌝)}
                {APPLY (SND ⌜ l ⌝) ⌜ i ⌝}
                c5
                (SEQ-AX⇓₁from-to {u𝕎 r n m (proj₁ c2)} {APPLY (SND ⌜ l ⌝) ⌜ i ⌝} (CTerm.closed (#APPLY (#SND l) i))))
  where
    c1 : Σ 𝕎· (λ w1 → ⌜ i ⌝ ⇓ NUM n from w to w1)
    c1 = ⇓→from-to (lower (ci w (⊑-refl· w)))

    e1 : w ⊑· fst c1
    e1 = #⇓from-to→⊑ {w} {fst c1} {i} {#NUM n} (snd c1)

    c2 : Σ 𝕎· (λ w2 → FST ⌜ l ⌝ ⇓ NUM m from (fst c1) to w2)
    c2 = ⇓→from-to (lower (#⇛-FST-PAIR2 l k f (#NUM m) w cl ck (fst c1) e1))

    c3 : IFLT ⌜ i ⌝ (FST ⌜ l ⌝) AX (set⊥ r) ⇓ IFLT (NUM n) (NUM m) AX (set⊥ r) from w to (fst c2)
    c3 = IFLT⇓₃ {w} {fst c1} {fst c2} {n} {m} {⌜ i ⌝} {FST ⌜ l ⌝} {AX} {set⊥ r} (snd c1) (snd c2)

    c4 : IFLT ⌜ i ⌝ (FST ⌜ l ⌝) AX (set⊥ r) ⇓ AX from w to u𝕎 r n m (fst c2)
    c4 = ⇓-trans₂
           {w} {fst c2} {u𝕎 r n m (fst c2)}
           {IFLT ⌜ i ⌝ (FST ⌜ l ⌝) AX (set⊥ r)}
           {IFLT (NUM n) (NUM m) AX (set⊥ r)}
           {AX}
           c3
           (IFLT-NUM-AX-CHOOSE⇓ r n m (fst c2))

    c5 : genericI r (FST ⌜ l ⌝) (SND ⌜ l ⌝) ⌜ i ⌝ ⇓ SEQ AX (APPLY (SND ⌜ l ⌝) ⌜ i ⌝) from w to u𝕎 r n m (fst c2)
    c5 = SEQ⇓₁
           {w} {u𝕎 r n m (fst c2)}
           {IFLT ⌜ i ⌝ (FST ⌜ l ⌝) AX (set⊥ r)}
           {AX}
           {APPLY (SND ⌜ l ⌝) ⌜ i ⌝}
           c4


#APPLY-#generic⇛ : (r : Name) (l i k f : CTerm) (w : 𝕎·) (m n : ℕ)
                    → l #⇛ #PAIR k f at w
                    → i #⇛ #NUM n at w
                    → k #⇛ #NUM m at w
                    → #APPLY (#generic r l) i #⇛ #APPLY (#SND l) i at w
#APPLY-#generic⇛ r l i k f w m n cl ci ck w1 e1 =
  lift (⇓-from-to→⇓ {w1} {u𝕎 r n m (fst c)} (snd c))
  where
    c : Σ 𝕎· (λ w' → #APPLY (#generic r l) i #⇓ #APPLY (#SND l) i from w1 to u𝕎 r n m w')
    c = #APPLY-#generic⇓2 r l i k f w1 m n (∀𝕎-mon e1 cl) (∀𝕎-mon e1 ci) (∀𝕎-mon e1 ck)


equalInType-NAT-#⇛ : (i : ℕ) (w : 𝕎·) (a1 a2 b1 b2 : CTerm)
                      → a1 #⇛ a2 at w
                      → b1 #⇛ b2 at w
                      → equalInType i w #NAT a2 b2
                      → equalInType i w #NAT a1 b1
equalInType-NAT-#⇛ i w a1 a2 b1 b2 c1 c2 eqi =
  →equalInType-NAT i w a1 b1 (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w a2 b2 eqi))
  where
    aw : ∀𝕎 w (λ w' e' → NATeq w' a2 b2 → NATeq w' a1 b1)
    aw w1 e1 (n , d1 , d2) =
      n ,
      #⇛-trans {w1} {a1} {a2} {#NUM n} (∀𝕎-mon e1 c1) d1 ,
      #⇛-trans {w1} {b1} {b2} {#NUM n} (∀𝕎-mon e1 c2) d2


{--
equalInType i w2 #NAT (#APPLY g1 i) (#APPLY g2 i)
a1 #⇛ #APPLY f1 i at w
f1 #⇛ g1 at w
equalInType i w2 #NAT a1 a2
--}


LISTNATeq : (i : ℕ) → wper
LISTNATeq i w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    NATeq w a1 a2
    × equalInType i w #BAIRE b1 b2
    × f #⇛ (#PAIR a1 b1) at w
    × g #⇛ (#PAIR a2 b2) at w))))


equalInType-LIST-NAT→ : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                         → equalInType i w (#LIST #NAT) f g
                         → □· w (λ w' _ → LISTNATeq i w' f g)
equalInType-LIST-NAT→ i w f g eqi = Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-PROD→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → PRODeq (equalInType i w' #NAT) (equalInType i w' (#FUN #NAT #NAT)) w' f g
                       → □· w' (↑wPred' (λ w'' _ → LISTNATeq i w'' f g) e'))
    aw w1 e1 (k1 , k2 , f1 , f2 , ek , ef , c1 , c2) = Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 k1 k2 ek)
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' k1 k2
                             → ↑wPred' (λ w'' _ → LISTNATeq i w'' f g) e1 w' e')
        aw1 w2 e2 ek' e3 = k1 , k2 , f1 , f2 , ek' , equalInType-mon ef w2 e2 , ∀𝕎-mon e2 c1 , ∀𝕎-mon e2 c2


NATeq-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {a1 a2 : CTerm}
            → NATeq w1 a1 a2
            → NATeq w2 a1 a2
NATeq-mon {w1} {w2} e {a1} {a2} (n , c1 , c2) = n , ∀𝕎-mon e c1 , ∀𝕎-mon e c2


→equalInType-LIST-NAT : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                         → □· w (λ w' _ → LISTNATeq i w' f g)
                         → equalInType i w (#LIST #NAT) f g
→equalInType-LIST-NAT i w f g eqi =
  equalInType-PROD eqTypesNAT eqTypesBAIRE (Mod.∀𝕎-□Func M aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → LISTNATeq i w' f g
                        → PRODeq (equalInType i w' #NAT) (equalInType i w' #BAIRE) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , x , y , c1 , c2) =
      a1 , a2 , b1 , b2 ,
      →equalInType-NAT i w1 a1 a2 (Mod.∀𝕎-□ M λ w2 e2 → NATeq-mon {w1} {w2} e2 {a1} {a2} x) ,
      y , c1 , c2


SUC-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (SUC a , w) ≡ (SUC b , w'))
SUC-steps₁ {0} {w} {w'} {a} {b} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
SUC-steps₁ {suc k} {w} {w'} {a} {b} comp with is-NUM a
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w (suc k) tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (SUC a , w) ≡ (SUC b , w'))
    c with is-NUM a
    ... | inj₁ (x' , z) rewrite z = ⊥-elim (x x' refl)
    ... | inj₂ x' rewrite q = SUC-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


SUC⇓₁ : {w w' : 𝕎·} {a b : Term}
         → a ⇓ b from w to w'
         → SUC a ⇓ SUC b from w to w'
SUC⇓₁ {w} {w'} {a} {b} (k , comp) = SUC-steps₁ {k} {w} {w'} {a} {b} comp



SUC⇛₁ : {w : 𝕎·} {a a' : Term}
           → a ⇛ a' at w
           → SUC a ⇛ SUC a' at w
SUC⇛₁ {w} {a} {a'} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (SUC⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


SUC⇛₂ : {w : 𝕎·} {a : Term} {k : ℕ}
           → a ⇛ NUM k at w
           → SUC a ⇛ NUM (suc k) at w
SUC⇛₂ {w} {a} {k} comp w1 e1 = lift ?


APPEND∈LIST : (i : ℕ) (w : 𝕎·) (l n : CTerm)
               → ∈Type i w (#LIST #NAT) l
               → ∈Type i w #NAT n
               → ∈Type i w (#LIST #NAT) (#APPEND l n)
APPEND∈LIST i w l n ∈l ∈n =
            →equalInType-LIST-NAT i w (#APPEND l n) (#APPEND l n) (∀𝕎-□Func2 aw ∈l1 ∈n1)
  where
    ∈l1 : □· w (λ w' _ → LISTNATeq i w' l l)
    ∈l1 = equalInType-LIST-NAT→ i w l l ∈l

    ∈n1 : □· w (λ w' _ → NATeq w' n n)
    ∈n1 = equalInType-NAT→ i w n n ∈n

    aw : ∀𝕎 w (λ w' e' → LISTNATeq i w' l l → NATeq w' n n → LISTNATeq i w' (#APPEND l n) (#APPEND l n))
    aw w1 e1 (a1 , a2 , f1 , f2 , (m , z1 , z2) , x2 , c1 , c2) (k , d1 , d2) =
      #SUC a1 , #SUC a2 , #APPENDf a1 f1 n , #APPENDf a2 f2 n ,
      (suc m , {!!} , {!!}) , -- use SUC⇛₂
      {!!} ,
      {!!} ,
      {!!}


generic∈BAIRE : (i : ℕ) (w : 𝕎·) (r : Name) (l : CTerm)
                → ∈Type i w (#LIST #NAT) l
                → ∈Type i w #BAIRE (#generic r l)
generic∈BAIRE i w r l ∈l =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw1)
  where
    p1 : □· w (λ w' _ → LISTNATeq i w' l l)
    p1 = equalInType-LIST-NAT→ i w l l ∈l

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                        → equalInType i w' #NAT (#APPLY (#generic r l) a₁) (#APPLY (#generic r l) a₂))
    aw1 w1 e1 a₁ a₂ ea = equalInType-local (∀𝕎-□Func2 aw2 (Mod.↑□ M p1 e1) p2)
      where
        p2 : □· w1 (λ w' _ → NATeq w' a₁ a₂)
        p2 = equalInType-NAT→ i w1 a₁ a₂ ea

        aw2 : ∀𝕎 w1 (λ w' e' → ↑wPred (λ w'' _ → LISTNATeq i w'' l l) e1 w' e'
                             → NATeq w' a₁ a₂
                             → equalInType i w' #NAT (#APPLY (#generic r l) a₁) (#APPLY (#generic r l) a₂))
        aw2 w2 e2 (k1 , k2 , f1 , f2 , ek , ef , c1 , c2) (n , d1 , d2) = p5
          where
            p3 : equalInType i w2 #NAT (#APPLY f1 a₁) (#APPLY f2 a₂)
            p3 = equalInType-FUN→ ef w2 (⊑-refl· w2) a₁ a₂ (equalInType-mon ea w2 e2)

            q1 : #APPLY (#SND l) a₁ #⇛ #APPLY f1 a₁ at w2
            q1 = →-#⇛-#APPLY {w2} {#SND l} {f1} a₁ (#⇛-SND-PAIR l k1 f1 w2 c1)

            q2 : #APPLY (#SND l) a₂ #⇛ #APPLY f2 a₂ at w2
            q2 = →-#⇛-#APPLY {w2} {#SND l} {f2} a₂ (#⇛-SND-PAIR l k2 f2 w2 c2)

            p4 : equalInType i w2 #NAT (#APPLY (#SND l) a₁) (#APPLY (#SND l) a₂)
            p4 = equalInType-NAT-#⇛ i w2 (#APPLY (#SND l) a₁) (#APPLY f1 a₁) (#APPLY (#SND l) a₂) (#APPLY f2 a₂) q1 q2 p3

            p5 : equalInType i w2 #NAT (#APPLY (#generic r l) a₁) (#APPLY (#generic r l) a₂)
            p5 = equalInType-NAT-#⇛
                   i w2 (#APPLY (#generic r l) a₁) (#APPLY (#SND l) a₁) (#APPLY (#generic r l) a₂) (#APPLY (#SND l) a₂)
                   (#APPLY-#generic⇛ r l a₁ k1 f1 w2 (fst ek) n c1 d1 (fst (snd ek)))
                   (#APPLY-#generic⇛ r l a₂ k2 f2 w2 (fst ek) n c2 d2 (snd (snd ek)))
                   p4


APPLY-generic∈NAT : (i : ℕ) (w : 𝕎·) (r : Name) (F l : CTerm)
                    → ∈Type i w #FunBar F
                    → ∈Type i w (#LIST #NAT) l
                    → ∈Type i w #NAT (#APPLY F (#generic r l))
APPLY-generic∈NAT i w r F l ∈F ∈l = ∈F' w (⊑-refl· w) (#generic r l) (#generic r l) (generic∈BAIRE i w r l ∈l)
  where
    ∈F' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #BAIRE a₁ a₂ → equalInType i w' #NAT (#APPLY F a₁) (#APPLY F a₂))
    ∈F' = equalInType-FUN→ ∈F


sub-loopI≡ : (r : Name) (R l i : Term) (cR : # R) (cl : # l) (ci : # i)
             → sub i (loopI r R l (VAR 0))
                ≡ loopI r R l i
sub-loopI≡ r R l i cR cl ci
  rewrite #shiftUp 0 (ct i ci)
        | #shiftUp 0 (ct i ci)
        | #shiftUp 0 (ct i ci)
        | #shiftUp 0 (ct i ci)
        | #shiftUp 0 (ct i ci)
        | #shiftUp 0 (ct i ci)
        | #shiftUp 0 (ct R cR)
        | #shiftUp 0 (ct R cR)
        | #shiftUp 2 (ct R cR)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 2 (ct l cl)
        | #shiftUp 3 (ct l cl)
        | #shiftDown 1 (ct i ci)
        | #subv 3 i R cR
        | #subv 3 i l cl
        | #subv 4 i l cl
        | #shiftDown 3 (ct R cR)
        | #shiftDown 3 (ct l cl)
        | #shiftDown 4 (ct l cl) =
  refl


loopB⇓loopI : (w : 𝕎·) (r : Name) (i : ℕ) (R l : Term) (cR : # R) (cl : # l)
              → loopB r (NUM i) R l ⇓ loopI r R l (NUM i) from w to w
loopB⇓loopI w r i R l cR cl = 1 , ≡pair c refl
  where
    c : sub (NUM i) (loopI r (shiftUp 0 R) (shiftUp 0 l) (VAR 0)) ≡ loopI r R l (NUM i)
    c rewrite #shiftUp 0 (ct R cR)
            | #shiftUp 0 (ct l cl)
            | sub-loopI≡ r R l (NUM i) cR cl refl
            | #shiftUp 0 (ct l cl)
            | #shiftUp 0 (ct l cl)
            | #shiftUp 0 (ct R cR)
            | #shiftUp 0 (ct R cR)
            | #shiftUp 2 (ct R cR)
            | #shiftUp 0 (ct l cl)
            | #shiftUp 2 (ct l cl)
            | #shiftUp 3 (ct l cl) = refl


#APPLY-#loop#⇓3 : (r : Name) (F l : CTerm) (i : ℕ) (w : 𝕎·)
                  → #APPLY F (#generic r l) #⇛ #NUM i at w
                  → #APPLY (#loop r F) l #⇓ #loopI r (#loop r F) l i at w
#APPLY-#loop#⇓3 r F l i w c =
  ⇓-trans₁
    {w} {chooseT r w BTRUE}
    {APPLY (loop r ⌜ F ⌝) ⌜ l ⌝}
    {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
    {loopI r (loop r ⌜ F ⌝) ⌜ l ⌝ (NUM i)}
    (#APPLY-#loop#⇓2 r F l w)
    (⇓-from-to→⇓ {chooseT r w BTRUE} {fst c3} (snd c3))
  where
    c1 : Σ 𝕎· (λ w' → #APPLY F (#generic r l) #⇓ #NUM i from (chooseT r w BTRUE) to w')
    c1 = ⇓→from-to (lower (c (chooseT r w BTRUE) (choose⊑· r w (T→ℂ· BTRUE))))

    c2 : Σ 𝕎· (λ w' → loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝ ⇓ loopB r (NUM i) (loop r ⌜ F ⌝) ⌜ l ⌝ from (chooseT r w BTRUE) to w')
    c2 = fst c1 , LET⇓₁ {chooseT r w BTRUE} {fst c1} {APPLY ⌜ F ⌝ (generic r ⌜ l ⌝)} {NUM i} (snd c1)

    c3 : Σ 𝕎· (λ w' → loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝ ⇓ loopI r (loop r ⌜ F ⌝) ⌜ l ⌝ (NUM i) from (chooseT r w BTRUE) to w')
    c3 = fst c1 , ⇓-trans₂ {chooseT r w BTRUE} {proj₁ c1} {proj₁ c1} (snd c2)
                           (loopB⇓loopI (proj₁ c1) r i (loop r ⌜ F ⌝) ⌜ l ⌝ (CTerm.closed (#loop r F)) (CTerm.closed l))


-- This constrains all Res⊤ choices to be Booleans, and here just BTRUE or BFALSE
-- This will be satisfied by worldInstanceRef2, which is for example used by modInsanceKripkeRefBool
-- This uses Res⊤ as this is the restiction used by FRESH
c𝔹 : Set(lsuc(L))
c𝔹 = (name : Name) (w : 𝕎·)
      → compatible· name w Res⊤ -- (Resℕ nc)
      → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (getT 0 name w' ≡ just BTRUE ⊎ getT 0 name w' ≡ just BFALSE))


#APPLY-#loop#⇓4₁ : (r : Name) (F l : CTerm) (i : ℕ) (w : 𝕎·)
                   → getT 0 r w ≡ just BTRUE
                   → #loopI r (#loop r F) l i #⇓ #ETA (#NUM i) from w to w
#APPLY-#loop#⇓4₁ r F l i w g = 2 , c1
  where
    c1 : steps 2 (loopI r (loop r ⌜ F ⌝) ⌜ l ⌝ (NUM i) , w) ≡ (ETA (NUM i) , w)
    c1 rewrite g = refl


#APPLY-#loop#⇓5₁ : (r : Name) (F l : CTerm) (i : ℕ) (w : 𝕎·)
                   → getT 0 r w ≡ just BFALSE
                   → #loopI r (#loop r F) l i #⇓ #DIGAMMA (#loopR (#loop r F) l) from w to w
#APPLY-#loop#⇓5₁ r F l i w g = 2 , c1
  where
    c1 : steps 2 (loopI r (loop r ⌜ F ⌝) ⌜ l ⌝ (NUM i) , w) ≡ (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝) , w)
    c1 rewrite g
             | subNotIn AX (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) (CTerm.closed (#DIGAMMA (#loopR (#loop r F) l)))
             | #shiftUp 0 F
             | #shiftUp 3 F
             | #shiftUp 3 F
             | #shiftUp 5 F
             | #subv 5 AX ⌜ F ⌝ (CTerm.closed F)
             | #shiftDown 5 F
             | #shiftUp 0 l
             | #shiftUp 0 l
             | #shiftUp 0 l
             | #shiftUp 2 l
             | #shiftUp 3 l
             | #subv 2 AX ⌜ l ⌝ (CTerm.closed l)
             | #subv 3 AX ⌜ l ⌝ (CTerm.closed l)
             | #shiftDown 2 l
             | #shiftDown 3 l = refl

abstract

  #APPLY-#loop#⇓4 : (cb : c𝔹) (r : Name) (F l : CTerm) (i : ℕ) (w : 𝕎·)
                    → compatible· r w Res⊤
                    → #APPLY F (#generic r l) #⇛ #NUM i at w
                    → #APPLY (#loop r F) l #⇓ #ETA (#NUM i) at w
                       ⊎ #APPLY (#loop r F) l #⇓ #DIGAMMA (#loopR (#loop r F) l) at w
  #APPLY-#loop#⇓4 cb r F l i w compat c = d2 d1
    where
      c1 : Σ 𝕎· (λ w' → #APPLY (#loop r F) l #⇓ #loopI r (#loop r F) l i from w to w')
      c1 = ⇓→from-to (#APPLY-#loop#⇓3 r F l i w c)

      e1 : w ⊑· fst c1
      e1 = #⇓from-to→⊑ {w} {fst c1} {#APPLY (#loop r F) l} {#loopI r (#loop r F) l i} (snd c1)

      d1 : getT 0 r (fst c1) ≡ just BTRUE ⊎ getT 0 r (fst c1) ≡ just BFALSE
      d1 = lower (cb r w compat (fst c1) e1)

      d2 : (getT 0 r (fst c1) ≡ just BTRUE ⊎ getT 0 r (fst c1) ≡ just BFALSE)
           → #APPLY (#loop r F) l #⇓ #ETA (#NUM i) at w
              ⊎ #APPLY (#loop r F) l #⇓ #DIGAMMA (#loopR (#loop r F) l) at w
      d2 (inj₁ x) =
        inj₁ (#⇓-trans₁
                {w} {fst c1} {#APPLY (#loop r F) l} {#loopI r (#loop r F) l i} {#ETA (#NUM i)}
                (snd c1)
                (⇓-from-to→⇓ {fst c1} {fst c1} (#APPLY-#loop#⇓4₁ r F l i (fst c1) x)))
      d2 (inj₂ x) =
        inj₂ (#⇓-trans₁
                {w} {fst c1} {#APPLY (#loop r F) l} {#loopI r (#loop r F) l i} {#DIGAMMA (#loopR (#loop r F) l)}
                (snd c1)
                (⇓-from-to→⇓ {fst c1} {fst c1} (#APPLY-#loop#⇓5₁ r F l i (fst c1) x)))


INL∈IndBarB : (i : ℕ) (w : 𝕎·) (k : ℕ) → ∈Type i w #IndBarB (#INL (#NUM k))
INL∈IndBarB i w k =
  →equalInType-UNION
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #NUM k , #NUM k , inj₁ (#compAllRefl (#INL (#NUM k)) w' , #compAllRefl (#INL (#NUM k)) w' , NUM-equalInType-NAT i w' k)))


INR∈IndBarB : (i : ℕ) (w : 𝕎·) → ∈Type i w #IndBarB (#INR #AX)
INR∈IndBarB i w =
  →equalInType-UNION
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #AX , #AX , inj₂ (#compAllRefl (#INR #AX) w' , #compAllRefl (#INR #AX) w' , →equalInType-TRUE i {w'} {#AX} {#AX})))


sub0-IndBarC≡ : (a : CTerm) → sub0 a #IndBarC ≡ #DECIDE a #[0]VOID #[0]NAT!
sub0-IndBarC≡ a = CTerm≡ (≡DECIDE x refl refl)
  where
    x : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    x rewrite #shiftUp 0 a | #shiftDown 0 a = refl


#DECIDE-INL-VOID⇓ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INL a) #[0]VOID b #⇓ #VOID from w to w
#DECIDE-INL-VOID⇓ w a b = 1 , refl


#DECIDE-INL-VOID⇛ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INL a) #[0]VOID b #⇛! #VOID at w
#DECIDE-INL-VOID⇛ w a b w1 e1 = lift (#DECIDE-INL-VOID⇓ w1 a b)


#DECIDE-INR-NAT⇓ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b #[0]NAT! #⇓ #NAT! from w to w
#DECIDE-INR-NAT⇓ w a b = 1 , refl


#DECIDE-INR-NAT⇛ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b #[0]NAT! #⇛! #NAT! at w
#DECIDE-INR-NAT⇛ w a b w1 e1 = lift (#DECIDE-INR-NAT⇓ w1 a b)


equalInType-#⇛ : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                  → T #⇛! U at w
                  → equalInType i w T a b
                  → equalInType i w U a b
equalInType-#⇛ {i} {w} {T} {U} {a} {b} comp e =
  TSext-equalTypes-equalInType
    i w T U a b
    (equalTypes-#⇛-left-right {i} {w} {T} {T} {U} {T} (#⇛!-refl {w} {T}) comp (fst e)) e


equalInType-DECIDE-INL-VOID→ : (i : ℕ) (w : 𝕎·) (a b1 b2 : CTerm) (b : CTerm0)
                                → equalInType i w (#DECIDE (#INL a) #[0]VOID b) b1 b2
                                → ⊥
equalInType-DECIDE-INL-VOID→ i w a b1 b2 b e =
  ¬equalInType-FALSE {w} {i} {b1} {b2} (equalInType-#⇛ (#DECIDE-INL-VOID⇛ w a b) e)


equalInType-DECIDE-INR-NAT→ : (i : ℕ) (w : 𝕎·) (a b1 b2 : CTerm) (b : CTerm0)
                                → equalInType i w (#DECIDE (#INR a) b #[0]NAT!) b1 b2
                                → equalInType i w #NAT! b1 b2
equalInType-DECIDE-INR-NAT→ i w a b1 b2 b e =
  equalInType-#⇛ (#DECIDE-INR-NAT⇛ w a b) e


APPLY-loopR-⇓ : (w1 w2 : 𝕎·) (R l b : CTerm) (k : ℕ)
                → b #⇓ #NUM k from w1 to w2
                → #APPLY (#loopR R l) b #⇓ #APPLY R (#APPEND l (#NUM k)) from w1 to w2
APPLY-loopR-⇓ w1 w2 R l b k comp =
  ⇓-trans₂
    {w1} {w1} {w2}
    {⌜ #APPLY (#loopR R l) b ⌝}
    {⌜ #loopRL b R l ⌝}
    {⌜ #APPLY R (#APPEND l (#NUM k)) ⌝}
    (1 , ≡pair c1 refl)
    (⇓-trans₂
       {w1} {w2} {w2}
       {⌜ #loopRL b R l ⌝}
       {⌜ #loopRL (#NUM k) R l ⌝}
       {⌜ #APPLY R (#APPEND l (#NUM k)) ⌝}
       (LET⇓ {⌜ b ⌝} {NUM k} ⌜ #[0]APPLY (#[0]shiftUp0 R) (#[0]APPEND (#[0]shiftUp0 l) #[0]VAR) ⌝ comp)
       (1 , ≡pair c2 refl))
-- #loopRL a R l
--APPLY⇓ {w1} {w2}
  where
    c1 : sub ⌜ b ⌝ (LET (VAR 0) (APPLY (shiftUp 0 (shiftUp 0 ⌜ R ⌝)) (APPEND (shiftUp 0 (shiftUp 0 ⌜ l ⌝)) (VAR 0))))
         ≡ ⌜ #loopRL b R l ⌝
    c1 rewrite #shiftUp 0 b
             | #shiftUp 0 b
             | #shiftUp 0 b
             | #shiftUp 0 R
             | #shiftUp 0 R
             | #subv 1 ⌜ b ⌝ ⌜ R ⌝ (CTerm.closed R)
             | #shiftDown 1 R
             | #shiftUp 0 l
             | #shiftUp 0 l
             | #shiftUp 0 l
             | #subv 1 ⌜ b ⌝ ⌜ l ⌝ (CTerm.closed l)
             | #subv 2 ⌜ b ⌝ ⌜ l ⌝ (CTerm.closed l)
             | #shiftDown 2 l
             | #shiftDown 1 l
             | #shiftDown 0 b = refl

    c2 : sub (NUM k) ⌜ #[0]APPLY (#[0]shiftUp0 R) (#[0]APPEND (#[0]shiftUp0 l) #[0]VAR) ⌝
         ≡ ⌜ #APPLY R (#APPEND l (#NUM k)) ⌝
    c2 rewrite #shiftUp 0 R
             | #shiftUp 0 l
             | #shiftUp 0 l
             | #subv 0 (NUM k) ⌜ R ⌝ (CTerm.closed R)
             | #subv 0 (NUM k) ⌜ l ⌝ (CTerm.closed l)
             | #subv 1 (NUM k) ⌜ l ⌝ (CTerm.closed l)
             | #shiftDown 0 R
             | #shiftDown 0 l
             | #shiftDown 1 l = refl


{--
APPLY-loopR-⇛ : (w : 𝕎·) (R l b : CTerm) (k : ℕ)
                 → b #⇛ #NUM k at w
                 → #APPLY (#loopR R l) b #⇛! #APPLY R (#APPEND l b) at w
APPLY-loopR-⇛ w R l b k comp w1 e1 = {!!} --lift (APPLY-loopR-⇓ w1 R l b)
--}

\end{code}
