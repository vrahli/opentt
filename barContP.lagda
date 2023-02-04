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


module barContP {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)



-- inspired by: https://arxiv.org/pdf/1608.03814.pdf
-- bib to be clarified


-- This constrains all Res⊤ choices to be Booleans, and here just BTRUE or BFALSE
-- This will be satisfied by worldInstanceRef2, which is for example used by modInsanceKripkeRefBool
-- This uses Res⊤ as this is the restiction used by FRESH
c𝔹 : Set(lsuc(L))
c𝔹 = (name : Name) (w : 𝕎·)
      → compatible· name w Res⊤ -- (Resℕ nc)
      → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (getT 0 name w' ≡ just BTRUE ⊎ getT 0 name w' ≡ just BFALSE))


-- This constrains all Res⊤ choices to be ℕs and here just (NUM k) for some k
-- This uses Res⊤ as this is the restiction used by FRESH
cℕ : Set(lsuc(L))
cℕ = (name : Name) (w : 𝕎·)
      → compatible· name w Res⊤ -- (Resℕ nc)
      → ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ k → getT 0 name w' ≡ just (NUM k))))


FunBar : Term
FunBar = BAIRE→NAT


#FunBar : CTerm
#FunBar = #BAIRE→NAT


IndBarB : Term
IndBarB = UNION! NAT UNIT


#UNIT : CTerm
#UNIT = ct UNIT refl


#IndBarB : CTerm
#IndBarB = #UNION! #NAT #UNIT


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
loopRR : Term → Term → Term
loopRR R xs = LAMBDA (LET (VAR 0) (APPLY R (APPEND xs (VAR 0))))


-- Recursive call used in DIGAMMA
loopR : Term → Term → Term
loopR R xs = loopRR (shiftUp 0 (shiftUp 0 R)) (shiftUp 0 (shiftUp 0 xs))


-- loopA's body
loopI : Name → Term → Term → Term → Term
loopI r R l i =
  IFLT (get0 r)
       (FST l)
       (ETA i)
       (DIGAMMA (loopR R l))


loopB : Name → Term → Term → Term → Term
loopB r a R xs = LET a (loopI r (shiftUp 0 R) (shiftUp 0 xs) (VAR 0))


-- l is a list, so its 2nd component is a function
loopA : Name → Term → Term → Term → Term
loopA r F R l = loopB r (appUpd r F (SND (shiftUp 0 (shiftUp 0 l)))) R l


-- this is similar to testM in continuity1.lagda
loopF : Name → Term → Term → Term → Term
loopF r F R l =
  SEQ (set0 r) -- we start by assuming that we have enough information
      (loopA r F R l)


loopL : Name →  Term → Term
loopL r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  LAMBDA (LAMBDA (loopF r bar (VAR 1) (VAR 0)))


loop : Name →  Term → Term
loop r bar = FIX (loopL r bar)


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


#loopRL : CTerm → CTerm → CTerm → CTerm
#loopRL a R l = #LET a (#[0]APPLY (#[0]shiftUp0 R) (#[0]APPEND (#[0]shiftUp0 l) #[0]VAR))


-- Recursive call used in DIGAMMA
#loopR : CTerm → CTerm → CTerm
#loopR R l = #LAMBDA (#[0]LET #[0]VAR (#[1]APPLY (#[1]shiftUp0 (#[0]shiftUp0 R)) (#[1]APPEND (#[1]shiftUp0 (#[0]shiftUp0 l)) #[1]VAR0)))


-- This is loopA's body
#loopI : Name →  CTerm → CTerm → ℕ → CTerm
#loopI r R l i =
  #IFLT (#get0 r)
        (#FST l)
        (#ETA (#NUM i))
        (#DIGAMMA (#loopR R l))


#loopA : Name →  CTerm → CTerm → CTerm → CTerm
#loopA r bar R l =
  #LET (#APPLY bar (#upd r (#SND (#shiftUp0 (#shiftUp0 l)))))
       (#[0]IFLT (#[0]get0 r)
                 (#[0]FST (#[0]shiftUp0 l))
                 (#[0]ETA #[0]VAR)
                 (#[0]DIGAMMA (#[0]LAMBDA (#[1]LET #[1]VAR0 (#[2]APPLY (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 R)))
                                                                       (#[2]APPEND (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 l))) #[2]VAR0))))))


#loopF : Name →  CTerm → CTerm → CTerm → CTerm
#loopF r F R l =
  -- 0 is the argument (the list), and 1 is the recursive call
  #SEQ (#set0 r) (#loopA r F R l)


#[1]set0 : (name : Name) → CTerm1
#[1]set0 name = ct1 (set0 name) c
  where
    c : #[ 0 ∷ [ 1 ] ] set0 name
    c = refl


lowerVars++ : (a b : List Var) → lowerVars (a ++ b) ≡ lowerVars a ++ lowerVars b
lowerVars++ [] b = refl
lowerVars++ (0 ∷ a) b = lowerVars++ a b
lowerVars++ (suc x ∷ a) b rewrite lowerVars++ a b = refl


lowerVars-fvars-shiftUp≡0 : (t : Term) → lowerVars (fvars (shiftUp 0 t)) ≡ fvars t
lowerVars-fvars-shiftUp≡0 t rewrite fvars-shiftUp≡ 0 t | loweVars-suc (fvars t) = refl


fvars-upd : (name : Name) (f : Term) → fvars (upd name f) ≡ lowerVars (lowerVars (fvars f))
fvars-upd name f
  rewrite lowerVars++ (fvars (shiftUp 0 f)) [ 1 ]
        | lowerVars-fvars-shiftUp≡0 f
        | lowerVars++ (fvars f) [ 0 ]
        | ++[] (lowerVars (fvars f)) = refl


#[1]upd : (name : Name) (f : CTerm3) → CTerm1
#[1]upd name f = ct1 (upd name ⌜ f ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] upd name ⌜ f ⌝
    c rewrite fvars-upd name ⌜ f ⌝ =
      ⊆→⊆?
        {lowerVars (lowerVars (fvars ⌜ f ⌝))}
        (lowerVars-fvars-[0,1,2]
          {lowerVars (fvars ⌜ f ⌝)}
          (lowerVars-fvars-[0,1,2,3] {fvars ⌜ f ⌝} (⊆?→⊆ {fvars ⌜ f ⌝} (CTerm3.closed f))))


#loop : Name →  CTerm → CTerm
#loop r bar =
  -- 0 is the argument (the list), and 1 is the recursive call
  #FIX (#LAMBDA (#[0]LAMBDA (#[1]SEQ (#[1]set0 r) F)))
  where
    F : CTerm1
    F = #[1]LET (#[1]APPLY ⌞ bar ⌟ (#[1]upd r (#[3]SND #[3]VAR2)))
                (#[2]IFLT (#[2]get0 r)
                          (#[2]FST #[2]VAR1)
                          (#[2]ETA #[2]VAR0)
                          (#[2]DIGAMMA (#[2]LAMBDA (#[3]LET #[3]VAR0 (#[4]APPLY #[4]VAR4 (#[4]APPEND #[4]VAR3 #[4]VAR0))))))


-- sanity checking
⌜#loopA⌝≡ : (r : Name) (F R l : CTerm) → ⌜ #loopA r F R l ⌝ ≡ loopA r ⌜ F ⌝ ⌜ R ⌝ ⌜ l ⌝
⌜#loopA⌝≡ r F R l = refl


-- sanity checking
⌜#loop⌝≡ : (r : Name) (F : CTerm) → ⌜ #loop r F ⌝ ≡ loop r ⌜ F ⌝
⌜#loop⌝≡ r F = refl


-- sanity checking
⌜#loopI⌝≡ : (r : Name) (R l : CTerm) (i : ℕ) → ⌜ #loopI r R l i ⌝ ≡ loopI r ⌜ R ⌝ ⌜ l ⌝ (NUM i)
⌜#loopI⌝≡ r R l i = refl


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


¬is-inj₁→is-inj₂ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B)
                    → ¬ is-inj₁ u
                    → is-inj₂ u
¬is-inj₁→is-inj₂ {I} {J} {A} {B} (inj₁ x) i = ⊥-elim (i tt)
¬is-inj₁→is-inj₂ {I} {J} {A} {B} (inj₂ x) i = tt


¬is-inj₂→is-inj₁ : {I J : Level} {A : Set(I)} {B : Set(J)} (u : A ⊎ B)
                    → ¬ is-inj₂ u
                    → is-inj₁ u
¬is-inj₂→is-inj₁ {I} {J} {A} {B} (inj₁ x) i = tt
¬is-inj₂→is-inj₁ {I} {J} {A} {B} (inj₂ x) i = ⊥-elim (i tt)


isFinPath→¬isInfPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B)
                        → isFinPath {i} {w} {A} {B} p
                        → ¬ isInfPath {i} {w} {A} {B} p
isFinPath→¬isInfPath {i} {w} {A} {B} p (n , fin) inf = is-inj₁→¬is-inj₂ (p n) (inf n) fin


¬isFinPath→isInfPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B)
                        → ¬ isFinPath {i} {w} {A} {B} p
                        → isInfPath {i} {w} {A} {B} p
¬isFinPath→isInfPath {i} {w} {A} {B} p fin n = ¬is-inj₂→is-inj₁ (p n) (λ x → fin (n , x))


shiftPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B) → path i w A B
shiftPath {i} {w} {A} {B} p k = p (suc k)



-- Defines what it means for a path to be correct w.r.t. a W or M type -- up to n (with fuel)
correctPathN : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (t : CTerm) (p : path i w A B) (n : ℕ) → Set(lsuc L)
correctPathN {i} {w} {A} {B} t p 0 = Lift (lsuc L) ⊤
correctPathN {i} {w} {A} {B} t p (suc n) with p 0
... | inj₁ (a , b , ia , ib) =
  Σ CTerm (λ f →
    t #⇓ #SUP a f at w -- {--#⇛--} -- For W types
    × correctPathN {i} {w} {A} {B} (#APPLY f b) (shiftPath {i} {w} {A} {B} p) n)
... | inj₂ _ = Lift (lsuc L) ⊤


-- A path is correct, if it is so for all ℕs
correctPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (t : CTerm) (p : path i w A B) → Set(lsuc L)
correctPath {i} {w} {A} {B} t p = (n : ℕ) → correctPathN {i} {w} {A} {B} t p n


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
          → path i w A B
mb2path i w A B t u m 0 with branch.branchC m
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = inj₁ (a1 , b1 , equalInType-refl ea , equalInType-refl eb)
mb2path i w A B t u m (suc n) with branch.branchC m
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) = mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n


correctN-mb2path : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t u : CTerm)
                   (b : branch (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u)
                   (n : ℕ)
                   → correctPathN {i} {w} {A} {B} t (mb2path i w A B t u b) n
correctN-mb2path i w A B t u b 0 = lift tt
correctN-mb2path i w A B t u b (suc n) with branch.branchC b
... | (a1 , f1 , b1 , a2 , f2 , b2 , ea , c1 , c2 , eb , q) =
  f1 , c1 , correctN-mb2path i w A B (#APPLY f1 b1) (#APPLY f2 b2) q n


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


m2w : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t : CTerm)
      → ∀𝕎 w (λ w' _ → isType i w' A)
      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
      → ∀𝕎 w (λ w' _ → (p : path i w' A B) → correctPath {i} {w'} {A} {B} t p → isFinPath {i} {w'} {A} {B} p)
      → ∈Type i w (#MT A B) t
      → ∈Type i w (#WT A B) t
m2w i w A B t eqta eqtb cond h =
  →equalInType-W i w A B t t eqta eqtb (Mod.∀𝕎-□Func M aw q)
  where
    q : □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    q = equalInType-M→ i w A B t t h

    aw : ∀𝕎 w (λ w' e' → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t
                       → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    aw w' e' z = m2wa i w' A B t t (cond w' e') z


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
        | #shiftDown 4 (ct l cl)
        | #shiftUp 6 (ct F cF)
        | #subv 7 l F cF
        | #shiftDown 7 (ct F cF)
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
                  → #APPLY (#loop r F) l #⇓ #loopA r F (#loop r F) l from w to (chooseT r w N0)
#APPLY-#loop#⇓2 r F l w =
  ⇓-trans₂ {w} {w} {chooseT r w N0}
           {APPLY (loop r ⌜ F ⌝) ⌜ l ⌝}
           {loopF r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
           {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
           (#APPLY-#loop#⇓1 r F l w)
           (step-⇓-from-to-trans {w} {chooseT r w N0} {chooseT r w N0}
                                 {loopF r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
                                 {SEQ AX (loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝)}
                                 {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
                                 refl
                                 (SEQ-AX⇓₁from-to {chooseT r w N0} {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
                                                  (CTerm.closed (#loopA r F (#loop r F) l))))


{--
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
--}


{--
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
--}


𝕎< : (r : Name) (n : ℕ) (w w1 w2 : 𝕎·) → 𝕎·
𝕎< r n w w1 w2 with getT 0 r w
... | just u with is-NUM u
... |    inj₁ (m , q) with m <? n
... |       yes p = w2
... |       no p = w1
𝕎< r n w w1 w2 | just u | inj₂ q = w1
𝕎< r n w w1 w2 | nothing = w1


u𝕎 : (r : Name) (n : ℕ) (w : 𝕎·) → 𝕎·
u𝕎 r n w = 𝕎< r n w w (chooseT r w (NUM n))


{--
IFLT⇓𝕎< : {w w1 w2 : 𝕎·} {a b c : Term} {n : ℕ}
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
--}


APPLY-upd⇓ : (r : Name) (w : 𝕎·) (f i : Term) (ci : # i) (cf : # f)
             → APPLY (upd r f) i ⇓ LET i (SEQ (updGt r (VAR 0)) (APPLY f (VAR 0))) from w to w
APPLY-upd⇓ r w f i ci cf = 1 , ≡pair c refl
  where
    c : sub i (LET (VAR 0) (SEQ (updGt r (VAR 0)) (APPLY f (VAR 0)))) ≡ LET i (SEQ (updGt r (VAR 0)) (APPLY f (VAR 0)))
    c rewrite #shiftUp 0 (ct i ci)
            | #shiftUp 0 (ct i ci)
            | #shiftUp 0 (ct i ci)
            | #shiftUp 0 (ct f cf)
            | #subv 2 i f cf
            | #shiftDown 0 (ct i ci)
            | #shiftDown 2 (ct f cf) = refl


updBody-LET⇓ : (r : Name) (w : 𝕎·) (f : Term) (n : ℕ) (cf : # f)
               → LET (NUM n) (SEQ (updGt r (VAR 0)) (APPLY f (VAR 0))) ⇓ SEQ (updGt r (NUM n)) (APPLY f (NUM n)) from w to w
updBody-LET⇓ r w f n cf = 1 , ≡pair c refl
  where
    c : sub (NUM n) (SEQ (updGt r (VAR 0)) (APPLY f (VAR 0))) ≡ SEQ (updGt r (NUM n)) (APPLY f (NUM n))
    c rewrite #shiftUp 0 (ct f cf)
            | #subv 1 (NUM n) f cf
            | #shiftDown 1 (ct f cf) = refl


SEQ-updtGt-step : (r : Name) (w : 𝕎·) (n m : ℕ) (t : Term)
                  → getT 0 r w ≡ just (NUM m)
                  → compatible· r w Res⊤
                  → Σ ℕ (λ k → steps (suc (suc k)) (SEQ (updGt r (NUM n)) t , w) ≡ (SEQ AX t , u𝕎 r n w))
SEQ-updtGt-step r w n m t gt0 compat with getT 0 r w
... | just u with is-NUM u
... |    inj₁ (m , q) with m <? n
... |       yes p = 1 , refl
... |       no p = 0 , refl
SEQ-updtGt-step r w n m t gt0 compat | just u | inj₂ q = ⊥-elim (q m (just-inj gt0))
SEQ-updtGt-step r w n m t gt0 compat | nothing = ⊥-elim (¬just≡nothing (sym gt0))


SEQ-updtGt⇓₁ : (cn : cℕ) (r : Name) (w : 𝕎·) (n : ℕ) (t : Term)
               → compatible· r w Res⊤
               → SEQ (updGt r (NUM n)) t ⇓ SEQ AX t from w to u𝕎 r n w
SEQ-updtGt⇓₁ cn r w n t compat = suc (suc (fst c)) , snd c
  where
    g : Σ ℕ (λ m → getT 0 r w ≡ just (NUM m))
    g = lower (cn r w compat w (⊑-refl· w))

    c : Σ ℕ (λ k → steps (suc (suc k)) (SEQ (updGt r (NUM n)) t , w) ≡ (SEQ AX t , u𝕎 r n w))
    c = SEQ-updtGt-step r w n (fst g) t (snd g) compat


SEQ-updtGt⇓ : (cn : cℕ) (r : Name) (w : 𝕎·) (n : ℕ) (t : Term) (clt : # t)
               → compatible· r w Res⊤
               → SEQ (updGt r (NUM n)) t ⇓ t from w to u𝕎 r n w
SEQ-updtGt⇓ cn r w n t clt compat =
  ⇓-trans₂
    {w} {u𝕎 r n w} {u𝕎 r n w}
    {SEQ (updGt r (NUM n)) t} {SEQ AX t} {t}
    (SEQ-updtGt⇓₁ cn r w n t compat)
    (SEQ-AX⇓₁from-to {u𝕎 r n w} {t} clt)


#APPLY-#upd⇓2 : (cn : cℕ) (r : Name) (i f : CTerm) (w : 𝕎·) (n : ℕ)
                → compatible· r w Res⊤
                → i #⇛ #NUM n at w
                → Σ 𝕎· (λ w' → #APPLY (#upd r f) i #⇓ #APPLY f (#NUM n) from w to u𝕎 r n w')
#APPLY-#upd⇓2 cn r i f w n compat ci =
  fst c1 , -- LET⇓₁
  ⇓-trans₂
    {w} {w} {u𝕎 r n (fst c1)}
    {APPLY (upd r ⌜ f ⌝) ⌜ i ⌝}
    {LET ⌜ i ⌝ (SEQ (updGt r (VAR 0)) (APPLY ⌜ f ⌝ (VAR 0)))}
    {APPLY ⌜ f ⌝ (NUM n)}
    (APPLY-upd⇓ r w ⌜ f ⌝ ⌜ i ⌝ (CTerm.closed i) (CTerm.closed f))
    (⇓-trans₂
       {w} {fst c1} {u𝕎 r n (fst c1)}
       {LET ⌜ i ⌝ (SEQ (updGt r (VAR 0)) (APPLY ⌜ f ⌝ (VAR 0)))}
       {LET (NUM n) (SEQ (updGt r (VAR 0)) (APPLY ⌜ f ⌝ (VAR 0)))}
       {APPLY ⌜ f ⌝ (NUM n)}
       (LET⇓₁ {w} {fst c1} {⌜ i ⌝} {NUM n} {SEQ (updGt r (VAR 0)) (APPLY ⌜ f ⌝ (VAR 0))} (snd c1))
       (⇓-trans₂
         {fst c1} {fst c1} {u𝕎 r n (fst c1)}
         {LET (NUM n) (SEQ (updGt r (VAR 0)) (APPLY ⌜ f ⌝ (VAR 0)))}
         {SEQ (updGt r (NUM n)) (APPLY ⌜ f ⌝ (NUM n))}
         {APPLY ⌜ f ⌝ (NUM n)}
         (updBody-LET⇓ r (fst c1) ⌜ f ⌝ n (CTerm.closed f))
         (SEQ-updtGt⇓ cn r (fst c1) n (APPLY ⌜ f ⌝ (NUM n)) (CTerm.closed (#APPLY f (#NUM n))) (⊑-compatible· e1 compat))))
  where
    c1 : Σ 𝕎· (λ w1 → ⌜ i ⌝ ⇓ NUM n from w to w1)
    c1 = ⇓→from-to (lower (ci w (⊑-refl· w)))

    e1 : w ⊑· fst c1
    e1 = #⇓from-to→⊑ {w} {fst c1} {i} {#NUM n} (snd c1)


#APPLY-#upd⇛ : (cn : cℕ) (r : Name) (i f : CTerm) (w : 𝕎·) (n : ℕ)
                → compatible· r w Res⊤
                → i #⇛ #NUM n at w
                → #APPLY (#upd r f) i #⇛ #APPLY f (#NUM n) at w
#APPLY-#upd⇛ cn r i f w n compat ci w1 e1 =
  lift (⇓-from-to→⇓ {w1} {u𝕎 r n (fst c)} (snd c))
  where
    c : Σ 𝕎· (λ w' → #APPLY (#upd r f) i #⇓ #APPLY f (#NUM n) from w1 to u𝕎 r n w')
    c = #APPLY-#upd⇓2 cn r i f w1 n (⊑-compatible· e1 compat) (∀𝕎-mon e1 ci)


{--
equalInType i w2 #NAT (#APPLY g1 i) (#APPLY g2 i)
a1 #⇛ #APPLY f1 i at w
f1 #⇛ g1 at w
equalInType i w2 #NAT a1 a2
--}


upd∈BAIRE : (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (f : CTerm)
             → compatible· r w Res⊤
             → ∈Type i w #BAIRE f
             → ∈Type i w #BAIRE (#upd r f)
upd∈BAIRE cn i w r f compat f∈ =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw1)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                        → equalInType i w' #NAT (#APPLY (#upd r f) a₁) (#APPLY (#upd r f) a₂))
    aw1 w1 e1 a₁ a₂ ea = equalInType-local (Mod.∀𝕎-□Func M aw p2) {--equalInType-local (∀𝕎-□Func2 aw2 (Mod.↑□ M p1 e1) p2)--}
      where
        p2 : □· w1 (λ w' _ → NATeq w' a₁ a₂)
        p2 = equalInType-NAT→ i w1 a₁ a₂ ea

        aw : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → equalInType i w' #NAT (#APPLY (#upd r f) a₁) (#APPLY (#upd r f) a₂))
        aw w2 e2 (k , c1 , c2) = →equalInType-NAT i w2 (#APPLY (#upd r f) a₁) (#APPLY (#upd r f) a₂) (Mod.∀𝕎-□Func M aw2 p3)
          where
            p3 : □· w2 (λ w' _ → NATeq w' (#APPLY f (#NUM k)) (#APPLY f (#NUM k)))
            p3 = equalInType-NAT→
                   i w2 (#APPLY f (#NUM k)) (#APPLY f (#NUM k))
                   (equalInType-FUN→ f∈ w2 (⊑-trans· e1 e2) (#NUM k) (#NUM k) (NUM-equalInType-NAT i w2 k))

            aw2 : ∀𝕎 w2 (λ w' e' → NATeq w' (#APPLY f (#NUM k)) (#APPLY f (#NUM k))
                                  → NATeq w' (#APPLY (#upd r f) a₁) (#APPLY (#upd r f) a₂))
            aw2 w3 e3 (j , d1 , d2) =
              j ,
              ⇛-trans (#APPLY-#upd⇛ cn r a₁ f w3 k (⊑-compatible· (⊑-trans· e1 (⊑-trans· e2 e3)) compat) (∀𝕎-mon e3 c1)) d1 ,
              ⇛-trans (#APPLY-#upd⇛ cn r a₂ f w3 k (⊑-compatible· (⊑-trans· e1 (⊑-trans· e2 e3)) compat) (∀𝕎-mon e3 c2)) d2


APPLY-upd∈NAT : (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F f : CTerm)
                 → compatible· r w Res⊤
                 → ∈Type i w #FunBar F
                 → ∈Type i w #BAIRE f
                 → ∈Type i w #NAT (#APPLY F (#upd r f))
APPLY-upd∈NAT cn i w r F f compat F∈ f∈ = F∈' w (⊑-refl· w) (#upd r f) (#upd r f) (upd∈BAIRE cn i w r f compat f∈)
  where
    F∈' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #BAIRE a₁ a₂ → equalInType i w' #NAT (#APPLY F a₁) (#APPLY F a₂))
    F∈' = equalInType-FUN→ F∈


INL∈IndBarB : (i : ℕ) (w : 𝕎·) (k : ℕ) → ∈Type i w #IndBarB (#INL (#NUM k))
INL∈IndBarB i w k =
  →equalInType-UNION!
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #NUM k , #NUM k , inj₁ (#⇛!-refl {w'} {#INL (#NUM k)} ,
                                                    #⇛!-refl {w'} {#INL (#NUM k)} ,
                                                    NUM-equalInType-NAT i w' k)))


INR∈IndBarB : (i : ℕ) (w : 𝕎·) → ∈Type i w #IndBarB (#INR #AX)
INR∈IndBarB i w =
  →equalInType-UNION!
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #AX , #AX , inj₂ (#⇛!-refl {w'} {#INR #AX} ,
                                              #⇛!-refl {w'} {#INR #AX} ,
                                              →equalInType-TRUE i {w'} {#AX} {#AX})))


sub0-IndBarC≡ : (a : CTerm) → sub0 a #IndBarC ≡ #DECIDE a #[0]VOID #[0]NAT!
sub0-IndBarC≡ a = CTerm≡ (≡DECIDE x refl refl)
  where
    x : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    x rewrite #shiftUp 0 a | #shiftDown 0 a = refl


#DECIDE-INL-VOID⇓ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INL a) #[0]VOID b #⇓ #VOID from w to w
#DECIDE-INL-VOID⇓ w a b = 1 , refl


#DECIDE-INL-VOID⇛ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INL a) #[0]VOID b #⇛! #VOID at w
#DECIDE-INL-VOID⇛ w a b w1 e1 = lift (#DECIDE-INL-VOID⇓ w1 a b)


#DECIDE⇛INL-VOID⇛ : (w : 𝕎·) (x a : CTerm) (b : CTerm0)
                     → x #⇛ #INL a at w
                     → #DECIDE x #[0]VOID b #⇛ #VOID at w
#DECIDE⇛INL-VOID⇛ w x a b comp =
  #⇛-trans
    {w} {#DECIDE x #[0]VOID b} {#DECIDE (#INL a) #[0]VOID b} {#VOID}
    (DECIDE⇛₁ {w} {⌜ x ⌝} {⌜ #INL a ⌝} {⌜ #[0]VOID ⌝} {⌜ b ⌝} comp)
    (#⇛!-#⇛ {w} {#DECIDE (#INL a) #[0]VOID b} {#VOID} (#DECIDE-INL-VOID⇛ w a b))


#DECIDE⇛INL-VOID⇛! : (w : 𝕎·) (x a : CTerm) (b : CTerm0)
                       → x #⇛! #INL a at w
                       → #DECIDE x #[0]VOID b #⇛! #VOID at w
#DECIDE⇛INL-VOID⇛! w x a b comp =
  #⇛!-trans
    {w} {#DECIDE x #[0]VOID b} {#DECIDE (#INL a) #[0]VOID b} {#VOID}
    (DECIDE⇛!₁ {w} {⌜ x ⌝} {⌜ #INL a ⌝} {⌜ #[0]VOID ⌝} {⌜ b ⌝} comp)
    (#DECIDE-INL-VOID⇛ w a b)


#DECIDE-INR-NAT⇓ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b #[0]NAT! #⇓ #NAT! from w to w
#DECIDE-INR-NAT⇓ w a b = 1 , refl


#DECIDE-INR-NAT⇛ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b #[0]NAT! #⇛! #NAT! at w
#DECIDE-INR-NAT⇛ w a b w1 e1 = lift (#DECIDE-INR-NAT⇓ w1 a b)


#DECIDE⇛INR-NAT⇛ : (w : 𝕎·) (x a : CTerm) (b : CTerm0)
                     → x #⇛ #INR a at w
                     → #DECIDE x b #[0]NAT! #⇛ #NAT! at w
#DECIDE⇛INR-NAT⇛ w x a b comp =
  #⇛-trans
    {w} {#DECIDE x b #[0]NAT!} {#DECIDE (#INR a) b #[0]NAT!} {#NAT!}
    (DECIDE⇛₁ {w} {⌜ x ⌝} {⌜ #INR a ⌝} {⌜ b ⌝} {⌜ #[0]NAT! ⌝} comp)
    (#⇛!-#⇛ {w} {#DECIDE (#INR a) b #[0]NAT!} {#NAT!} (#DECIDE-INR-NAT⇛ w a b))


#DECIDE⇛INR-NAT⇛! : (w : 𝕎·) (x a : CTerm) (b : CTerm0)
                      → x #⇛! #INR a at w
                      → #DECIDE x b #[0]NAT! #⇛! #NAT! at w
#DECIDE⇛INR-NAT⇛! w x a b comp =
  #⇛!-trans
    {w} {#DECIDE x b #[0]NAT!} {#DECIDE (#INR a) b #[0]NAT!} {#NAT!}
    (DECIDE⇛!₁ {w} {⌜ x ⌝} {⌜ #INR a ⌝} {⌜ b ⌝} {⌜ #[0]NAT! ⌝} comp)
    (#DECIDE-INR-NAT⇛ w a b)


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


INL→!∈Type-IndBarC : (i : ℕ) (w : 𝕎·) (x a b : CTerm)
                     → x #⇛! #INL a at w
                     → ¬ ∈Type i w (sub0 x #IndBarC) b
INL→!∈Type-IndBarC i w x a b comp j rewrite sub0-IndBarC≡ x =
  ¬equalInType-FALSE j1
  where
    j1 : ∈Type i w #VOID b
    j1 = equalInType-#⇛ (#DECIDE⇛INL-VOID⇛! w x a #[0]NAT! comp) j


INR→!∈Type-IndBarC : (i : ℕ) (w : 𝕎·) (x a b : CTerm)
                     → x #⇛! #INR a at w
                     → ∈Type i w (sub0 x #IndBarC) b
                     → □· w (λ w' _ → Σ ℕ (λ n → b #⇛! #NUM n at w'))
INR→!∈Type-IndBarC i w x a b comp j rewrite sub0-IndBarC≡ x =
  Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w b b j1)
  where
    j1 : ∈Type i w #NAT! b
    j1 = equalInType-#⇛ (#DECIDE⇛INR-NAT⇛! w x a #[0]VOID comp) j

    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' b b → Σ ℕ (λ n → b #⇛! #NUM n at w'))
    aw w1 e1 (n , c1 , c2) = n , c1


∈Type-IndBarB-IndBarC→ : (i : ℕ) (w : 𝕎·) (b c : CTerm)
                           → ∈Type i w #IndBarB b
                           → ∈Type i w (sub0 b #IndBarC) c
                           → □· w (λ w' _ → Σ CTerm (λ t → b #⇛! #INR t at w') × Σ ℕ (λ n → c #⇛! #NUM n at w'))
∈Type-IndBarB-IndBarC→ i w b c b∈ c∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-UNION!→ b∈))
  where
    aw : ∀𝕎 w (λ w' e' → UNION!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' b b
                        → Mod.□ M w' (↑wPred' (λ w'' _ → Σ CTerm (λ t → b #⇛! #INR t at w'') × Σ ℕ (λ n → c #⇛! #NUM n at w'')) e'))
    aw w1 e1 (x , y , inj₁ (c1 , c2 , eqi)) = ⊥-elim (INL→!∈Type-IndBarC i w1 b x c c1 (equalInType-mon c∈ w1 e1))
    aw w1 e1 (x , y , inj₂ (c1 , c2 , eqi)) =
      Mod.∀𝕎-□Func
        M
        (λ w2 e2 (n , cn) z → (x , ∀𝕎-mon e2 c1) , (n , cn))
        (INR→!∈Type-IndBarC i w1 b x c c1 (equalInType-mon c∈ w1 e1))


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
        | #shiftDown 4 (ct l cl)
        | #subv 2 i R cR
        | #subv 0 i l cl
        | #subv 2 i l cl
        | #shiftDown 0 (ct i ci)
        | #shiftDown 0 (ct l cl)
        | #shiftDown 2 (ct l cl)
        | #shiftDown 2 (ct R cR) =
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


shiftUp00 : (l : CTerm) → shiftUp 0 (shiftUp 0 ⌜ l ⌝) ≡ ⌜ l ⌝
shiftUp00 l rewrite #shiftUp 0 l | #shiftUp 0 l = refl


#APPLY-#loop#⇓3 : (r : Name) (F l : CTerm) (i : ℕ) (w : 𝕎·)
                  → #APPLY F (#upd r (#SND l)) #⇓ #NUM i at (chooseT r w N0)
                  → #APPLY (#loop r F) l #⇓ #loopI r (#loop r F) l i at w
#APPLY-#loop#⇓3 r F l i w c =
  ⇓-trans₁
    {w} {chooseT r w N0}
    {APPLY (loop r ⌜ F ⌝) ⌜ l ⌝}
    {loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝}
    {loopI r (loop r ⌜ F ⌝) ⌜ l ⌝ (NUM i)}
    (#APPLY-#loop#⇓2 r F l w)
    (⇓-from-to→⇓ {chooseT r w N0} {fst c1} c3)
  where
    c1 : Σ 𝕎· (λ w' → #APPLY F (#upd r (#SND l)) #⇓ #NUM i from (chooseT r w N0) to w')
    c1 = ⇓→from-to c

    c0 : appUpd r ⌜ F ⌝ (SND (shiftUp 0 (shiftUp 0 ⌜ l ⌝))) ⇓ NUM i from chooseT r w N0 to fst c1
    c0 rewrite shiftUp00 l = snd c1

    c2 : loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝ ⇓ loopB r (NUM i) (loop r ⌜ F ⌝) ⌜ l ⌝ from (chooseT r w N0) to fst c1
    c2 = LET⇓₁ {chooseT r w N0} {fst c1} {appUpd r ⌜ F ⌝ (SND (shiftUp 0 (shiftUp 0 ⌜ l ⌝)))} {NUM i} c0

    c3 : loopA r ⌜ F ⌝ (loop r ⌜ F ⌝) ⌜ l ⌝ ⇓ loopI r (loop r ⌜ F ⌝) ⌜ l ⌝ (NUM i) from (chooseT r w N0) to fst c1
    c3 = ⇓-trans₂ {chooseT r w N0} {fst c1} {fst c1} c2
                           (loopB⇓loopI (fst c1) r i (loop r ⌜ F ⌝) ⌜ l ⌝ (CTerm.closed (#loop r F)) (CTerm.closed l))


#APPLY-#loop#⇓4₁ : (r : Name) (F l k f : CTerm) (i : ℕ) (w : 𝕎·) (m n : ℕ)
                   → getT 0 r w ≡ just (NUM m)
                   → l #⇛ #PAIR k f at w
                   → k #⇛ #NUM n at w
                   → m < n
                   → Σ 𝕎· (λ w' → #loopI r (#loop r F) l i #⇓ #ETA (#NUM i) from w to w')
#APPLY-#loop#⇓4₁ r F l k f i w m n g cl ck mn =
  fst c1 , ⇓-trans₂ {w} {proj₁ c1} {proj₁ c1} c3 (step→⇓ (IFLT-NUM⇓< m n (fst c1) (ETA (NUM i)) (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) mn))
  where
    c1 : Σ 𝕎· (λ w' → #FST l #⇓ #NUM n from w to w')
    c1 = #⇓→from-to {w} {#FST l} {#NUM n} (lower (#⇛-FST-PAIR2 l k f (#NUM n) w cl ck w (⊑-refl· w)))

    c0 : steps 1 (get0 r , w) ≡ (NUM m , w)
    c0 rewrite g = refl

    c2 : #loopI r (#loop r F) l i #⇓ #IFLT (#NUM m) (#FST l) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop r F) l)) from w to w
    c2 = IFLT-NUM-1st⇓ {get0 r} {NUM m} (FST ⌜ l ⌝) (ETA (NUM i)) (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) (1 , c0)

    c3 : #loopI r (#loop r F) l i #⇓ #IFLT (#NUM m) (#NUM n) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop r F) l)) from w to fst c1
    c3 = ⇓-trans₂ {w} {w} {fst c1} c2 (IFLT-NUM-2nd⇓ m {FST ⌜ l ⌝} {NUM n} (ETA (NUM i)) (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) (snd c1))


#APPLY-#loop#⇓5₁ : (r : Name) (F l k f : CTerm) (i : ℕ) (w : 𝕎·) (m n : ℕ)
                   → getT 0 r w ≡ just (NUM m)
                   → l #⇛ #PAIR k f at w
                   → k #⇛ #NUM n at w
                   → ¬ m < n
                   → Σ 𝕎· (λ w' → #loopI r (#loop r F) l i #⇓ #DIGAMMA (#loopR (#loop r F) l) from w to w')
#APPLY-#loop#⇓5₁ r F l k f i w m n g cl ck mn =
  fst c1 , ⇓-trans₂ {w} {proj₁ c1} {proj₁ c1} c3 (step→⇓ (IFLT-NUM⇓¬< m n (fst c1) (ETA (NUM i)) (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) mn))
  where
    c1 : Σ 𝕎· (λ w' → #FST l #⇓ #NUM n from w to w')
    c1 = #⇓→from-to {w} {#FST l} {#NUM n} (lower (#⇛-FST-PAIR2 l k f (#NUM n) w cl ck w (⊑-refl· w)))

    c0 : steps 1 (get0 r , w) ≡ (NUM m , w)
    c0 rewrite g = refl

    c2 : #loopI r (#loop r F) l i #⇓ #IFLT (#NUM m) (#FST l) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop r F) l)) from w to w
    c2 = IFLT-NUM-1st⇓ {get0 r} {NUM m} (FST ⌜ l ⌝) (ETA (NUM i)) (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) (1 , c0)

    c3 : #loopI r (#loop r F) l i #⇓ #IFLT (#NUM m) (#NUM n) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop r F) l)) from w to fst c1
    c3 = ⇓-trans₂ {w} {w} {fst c1} c2 (IFLT-NUM-2nd⇓ m {FST ⌜ l ⌝} {NUM n} (ETA (NUM i)) (DIGAMMA (loopR (loop r ⌜ F ⌝) ⌜ l ⌝)) (snd c1))


<⊎¬ : (a b : ℕ) → a < b ⊎ ¬ a < b
<⊎¬ a b with a <? b
... | yes y = inj₁ y
... | no y = inj₂ y


abstract

  #APPLY-#loop#⇓4 : (cn : cℕ) (r : Name) (F l k f : CTerm) (i n : ℕ) (w : 𝕎·)
                    → compatible· r w Res⊤
                    → l #⇛ #PAIR k f at w
                    → k #⇛ #NUM n at w
                    → #APPLY F (#upd r (#SND l)) #⇓ #NUM i at (chooseT r w N0)
                    → #APPLY (#loop r F) l #⇓ #ETA (#NUM i) at w
                       ⊎ #APPLY (#loop r F) l #⇓ #DIGAMMA (#loopR (#loop r F) l) at w
  #APPLY-#loop#⇓4 cn r F l k f i n w compat compl compk c = d2 (<⊎¬ m n)
    where
      c1 : Σ 𝕎· (λ w' → #APPLY (#loop r F) l #⇓ #loopI r (#loop r F) l i from w to w')
      c1 = ⇓→from-to (#APPLY-#loop#⇓3 r F l i w c)

      e1 : w ⊑· fst c1
      e1 = #⇓from-to→⊑ {w} {fst c1} {#APPLY (#loop r F) l} {#loopI r (#loop r F) l i} (snd c1)

      d1 : Σ ℕ (λ j → getT 0 r (fst c1) ≡ just (NUM j))
      d1 = lower (cn r w compat (fst c1) e1)

      m : ℕ
      m = fst d1

      d2 : (m < n ⊎ ¬ m < n)
           → #APPLY (#loop r F) l #⇓ #ETA (#NUM i) at w
              ⊎ #APPLY (#loop r F) l #⇓ #DIGAMMA (#loopR (#loop r F) l) at w
      d2 (inj₁ x) =
        inj₁ (#⇓-trans₁
                {w} {fst c1} {#APPLY (#loop r F) l} {#loopI r (#loop r F) l i} {#ETA (#NUM i)}
                (snd c1)
                (Σ⇓-from-to→⇓ (#APPLY-#loop#⇓4₁ r F l k f i (fst c1) m n (snd d1) (∀𝕎-mon e1 compl) (∀𝕎-mon e1 compk) x)))
      d2 (inj₂ x) =
        inj₂ (#⇓-trans₁
                {w} {fst c1} {#APPLY (#loop r F) l} {#loopI r (#loop r F) l i} {#DIGAMMA (#loopR (#loop r F) l)}
                (snd c1)
                (Σ⇓-from-to→⇓ (#APPLY-#loop#⇓5₁ r F l k f i (fst c1) m n (snd d1) (∀𝕎-mon e1 compl) (∀𝕎-mon e1 compk) x)))


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


upd-SND∈BAIRE : (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (l : CTerm)
                 → compatible· r w Res⊤
                 → ∈Type i w (#LIST #NAT) l
                 → ∈Type i w #BAIRE (#upd r (#SND l))
upd-SND∈BAIRE cn i w r l compat l∈ =
  upd∈BAIRE cn i w r (#SND l) compat (∈LIST→SND i w l l∈)


\end{code}
