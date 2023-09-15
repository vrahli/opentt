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
open import encode


module barContP {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                (X : ChoiceExt W C)
                (N : NewChoice {L} W C K G)
                (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                (EM : ExcludedMiddle (lsuc(L)))
                (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)




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


FunBar : Term → Term
FunBar T = FUN (FUN NAT T) NAT


#FunBar : CTerm → CTerm
#FunBar T = #FUN (#FUN #NAT T) #NAT


IndBarB : Term
IndBarB = UNION₀! NAT UNIT


#UNIT : CTerm
#UNIT = ct UNIT refl


#IndBarB : CTerm
#IndBarB = #UNION₀! #NAT #UNIT


-- IndBarC uses NAT! because if DIGAMMAs are functions from NAT, then to prove that (loop ∈ coW -- see coSemM)
-- we need to jump to the 𝕎s at wihch the NATs are actual numbers, and we don't have members of the coW at the
-- current 𝕎
IndBarC : Term → Term
IndBarC T = DECIDE (VAR 0) VOID (NOWRITEMOD T)


#IndBarC : CTerm → CTerm0
#IndBarC T = #[0]DECIDE #[0]VAR #[1]VOID (#[1]shiftUp0 (#[0]shiftUp0 (#NOWRITEMOD T)))


IndBar : Term → Term
IndBar T = WT₀ IndBarB (IndBarC T)


#IndBar : CTerm → CTerm
#IndBar T = #WT₀ #IndBarB (#IndBarC T)


CoIndBar : Term → Term
CoIndBar T = MT₀ IndBarB (IndBarC T)


#CoIndBar : CTerm → CTerm
#CoIndBar T = #MT₀ #IndBarB (#IndBarC T)


ETA : Term → Term
ETA n = SUP (INL n) AX


DIGAMMA : Term → Term
DIGAMMA f = SUP (INR AX) f


barThesis : Term → Term
barThesis T = FUN (FunBar T) (IndBar T)


-- Recursive call used in DIGAMMA
loopR : Term → Term → Term → Term
loopR R k f =
  LAMBDA (LET (VAR 0)
              (LET (SUC (shiftUp 0 (shiftUp 0 k)))
                   (APPLY2 (shiftUp 0 (shiftUp 0 (shiftUp 0 R)))
                           (VAR 0)
                           (APPENDf (shiftUp 0 (shiftUp 0 (shiftUp 0 k))) (shiftUp 0 (shiftUp 0 (shiftUp 0 f))) (VAR 1)))))


loopII : Name → Term → Term → Term → Term → Term
loopII r R k f i =
  IFLT (get0 r)
       k
       (ETA i)
       (DIGAMMA (loopR R k f))


-- loopA's body
loopI : Name → Term → Term → Term → Term → Term
loopI r R k f i = IFLT i N0 BOT (loopII r R k f i) -- forces i to be a number


loopB : Name → Term → Term → Term → Term → Term
loopB r a R k f = LET a (loopI r (shiftUp 0 R) (shiftUp 0 k) (shiftUp 0 f) (VAR 0))


-- ⟨k,f⟩ is a list, so its 2nd component f is a function
loopA : Name → Term → Term → Term → Term → Term
loopA r F R k f = loopB r (appUpd r F (shiftUp 0 (shiftUp 0 f))) R k f


-- this is similar to testM in continuity1.lagda
loopF : Name → Term → Term → Term → Term → Term
loopF r F R k f =
  SEQ (set0 r) -- we start by assuming that we have enough information
      (loopA r F R k f)


νloopFB : Term → Term → Term → Term → Term
νloopFB F R k f = loopF 0 (shiftNameUp 0 F) (shiftNameUp 0 R) (shiftNameUp 0 k) (shiftNameUp 0 f)


νloopF : Term → Term → Term → Term → Term
νloopF F R k f = FRESH (νloopFB F R k f)


loopL : Term → Term
loopL F =
  -- 0 & 1 are the argument (the list: length (1) + function (0)), and 2 is the recursive call
  LAMBDA (LAMBDA (LAMBDA (νloopF (shiftUp 0 (shiftUp 0 (shiftUp 0 F))) (VAR 2) (VAR 1) (VAR 0))))


loop : Term → Term
loop bar = FIX (loopL bar)


#ETA : CTerm → CTerm
#ETA n = #SUP (#INL n) #AX


#[0]ETA : CTerm0 → CTerm0
#[0]ETA n = #[0]SUP (#[0]INL n) #[0]AX


#[2]ETA : CTerm2 → CTerm2
#[2]ETA n = #[2]SUP (#[2]INL n) #[2]AX


#[3]ETA : CTerm3 → CTerm3
#[3]ETA n = #[3]SUP (#[3]INL n) #[3]AX


#DIGAMMA : CTerm → CTerm
#DIGAMMA f = #SUP (#INR #AX) f


#[0]DIGAMMA : CTerm0 → CTerm0
#[0]DIGAMMA f = #[0]SUP (#[0]INR #[0]AX) f


#[2]DIGAMMA : CTerm2 → CTerm2
#[2]DIGAMMA f = #[2]SUP (#[2]INR #[2]AX) f


#[3]DIGAMMA : CTerm3 → CTerm3
#[3]DIGAMMA f = #[3]SUP (#[3]INR #[3]AX) f


#[0]loopRLLA : CTerm0 → CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]loopRLLA a R k f =
  #[0]APPLY2 R
             #[0]VAR
             (#[0]APPENDf k f a)


#loopRLL : CTerm → CTerm → CTerm → CTerm → CTerm → CTerm
#loopRLL j a R k f =
  #LET j (#[0]loopRLLA (#[0]shiftUp0 a) (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f))


#[0]loopRLL : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]loopRLL R k f =
  #[0]LET (#[0]SUC k)
          (#[1]APPLY2 (#[1]shiftUp0 R)
                      #[1]VAR0
                      (#[1]APPENDf (#[1]shiftUp0 k) (#[1]shiftUp0 f) #[1]VAR1))


#loopRL : CTerm → CTerm → CTerm → CTerm → CTerm
#loopRL a R k f =
  #LET a (#[0]loopRLL (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f))


#[0]loopRL : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]loopRL R k f =
  #[0]LET #[0]VAR
          (#[1]LET (#[1]SUC (#[1]shiftUp0 k))
                   (#[2]APPLY2 (#[2]shiftUp0 (#[1]shiftUp0 R))
                               #[2]VAR0
                               (#[2]APPENDf (#[2]shiftUp0 (#[1]shiftUp0 k))
                                            (#[2]shiftUp0 (#[1]shiftUp0 f))
                                            #[2]VAR1)))


-- Recursive call used in DIGAMMA
#loopR : CTerm → CTerm → CTerm → CTerm
#loopR R k f =
  #LAMBDA (#[0]loopRL (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f))


#loopII : Name →  CTerm → CTerm → CTerm → ℕ → CTerm
#loopII r R k f i =
  #IFLT (#get0 r)
         k
         (#ETA (#NUM i))
         (#DIGAMMA (#loopR R k f))


-- This is loopA's body
#loopI : Name →  CTerm → CTerm → CTerm → ℕ → CTerm
#loopI r R k f i = #IFLT (#NUM i) #N0 #BOT (#loopII r R k f i)


#loopA : Name →  CTerm → CTerm → CTerm → CTerm → CTerm
#loopA r bar R k f =
  #LET (#APPLY bar (#upd r (#shiftUp0 (#shiftUp0 f))))
       (#[0]IFLT #[0]VAR #[0]N0 #[0]BOT
                 (#[0]IFLT (#[0]get0 r)
                           (#[0]shiftUp0 k)
                           (#[0]ETA #[0]VAR)
                           (#[0]DIGAMMA (#[0]LAMBDA (#[1]LET #[1]VAR0
                                                             (#[2]LET (#[2]SUC (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 k))))
                                                                      (#[3]APPLY2 (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 R))))
                                                                                  #[3]VAR0
                                                                                  (#[3]APPENDf (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 k))))
                                                                                               (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 f))))
                                                                                               #[3]VAR1))))))))


#loopF : Name →  CTerm → CTerm → CTerm → CTerm → CTerm
#loopF r F R k f =
  #SEQ (#set0 r) (#loopA r F R k f)


#FRESH : CTerm → CTerm
#FRESH a = ct (FRESH ⌜ a ⌝) c
  where
    c : # FRESH ⌜ a ⌝
    c = CTerm.closed a


#[2]FRESH : CTerm2 → CTerm2
#[2]FRESH a = ct2 (FRESH ⌜ a ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] FRESH ⌜ a ⌝
    c = CTerm2.closed a


#νloopFB : CTerm → CTerm → CTerm → CTerm → CTerm
#νloopFB F R k f = #loopF 0 (#shiftNameUp 0 F) (#shiftNameUp 0 R) (#shiftNameUp 0 k) (#shiftNameUp 0 f)


#νloopF : CTerm → CTerm → CTerm → CTerm → CTerm
#νloopF F R k f = #FRESH (#νloopFB F R k f)


#[1]set0 : (name : Name) → CTerm1
#[1]set0 name = ct1 (set0 name) c
  where
    c : #[ 0 ∷ [ 1 ] ] set0 name
    c = refl


#[2]set0 : (name : Name) → CTerm2
#[2]set0 name = ct2 (set0 name) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] set0 name
    c = refl


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


#[2]upd : (name : Name) (f : CTerm4) → CTerm2
#[2]upd name f = ct2 (upd name ⌜ f ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] upd name ⌜ f ⌝
    c rewrite fvars-upd name ⌜ f ⌝ =
      ⊆→⊆?
        {lowerVars (lowerVars (fvars ⌜ f ⌝))}
        (lowerVars-fvars-[0,1,2,3]
          {lowerVars (fvars ⌜ f ⌝)}
          (lowerVars-fvars-[0,1,2,3,4] {fvars ⌜ f ⌝} (⊆?→⊆ {fvars ⌜ f ⌝} (CTerm4.closed f))))


#[2]shiftNameUp : ℕ → CTerm2 → CTerm2
#[2]shiftNameUp n t = ct2 (shiftNameUp n ⌜ t ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] shiftNameUp n (CTerm2.cTerm t)
    c rewrite fvars-shiftNameUp n (CTerm2.cTerm t) = CTerm2.closed t


#loop : CTerm → CTerm
#loop bar =
  -- 0&1 are the argument (the list): 1 is the length and 0 the function
  -- and 2 is the recursive call
  #FIX (#LAMBDA (#[0]LAMBDA (#[1]LAMBDA (#[2]FRESH (#[2]SEQ (#[2]set0 r) F)))))
  where
    r : Name
    r = 0

    F : CTerm2
    F = #[2]LET (#[2]APPLY (#[2]shiftNameUp 0 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 bar)))) (#[2]upd r #[4]VAR2))
                (#[3]IFLT #[3]VAR0 #[3]N0 #[3]BOT
                (#[3]IFLT (#[3]get0 r)
                          #[3]VAR2
                          (#[3]ETA #[3]VAR0)
                          (#[3]DIGAMMA (#[3]LAMBDA (#[4]LET #[4]VAR0
                                                            (#[5]LET (#[5]SUC #[5]VAR4)
                                                                     (#[6]APPLY2 #[6]VAR6
                                                                                 #[6]VAR0
                                                                                 (#[6]APPENDf #[6]VAR5 #[6]VAR4 #[6]VAR1))))))))


-- sanity checking
⌜#loopA⌝≡ : (r : Name) (F R k f : CTerm) → ⌜ #loopA r F R k f ⌝ ≡ loopA r ⌜ F ⌝ ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝
⌜#loopA⌝≡ r F R k f = refl


-- sanity checking
⌜#loopF⌝≡ : (r : Name) (F R k f : CTerm) → ⌜ #loopF r F R k f ⌝ ≡ loopF r ⌜ F ⌝ ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝
⌜#loopF⌝≡ r F R k f = refl


-- sanity checking
⌜#loopI⌝≡ : (r : Name) (R k f : CTerm) (i : ℕ) → ⌜ #loopI r R k f i ⌝ ≡ loopI r ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝ (NUM i)
⌜#loopI⌝≡ r R k f i = refl


-- sanity checking
⌜#loop⌝≡ : (F : CTerm) → ⌜ #loop F ⌝ ≡ loop ⌜ F ⌝
⌜#loop⌝≡ F = refl


-- sanity checking
⌜APPLY-loop⌝≡ : (F l : CTerm) → ⌜ #APPLY (#loop F) l ⌝ ≡ APPLY (loop ⌜ F ⌝) ⌜ l ⌝
⌜APPLY-loop⌝≡ F l = refl


-- sanity checking
⌜APPLY2-loop⌝≡ : (F k f : CTerm) → ⌜ #APPLY2 (#loop F) k f ⌝ ≡ APPLY2 (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝
⌜APPLY2-loop⌝≡ F k f = refl


-- sanity checking
⌜loopF-loop⌝≡ : (r : Name) (F k f : CTerm) → ⌜ #loopF r F (#loop F) k f ⌝ ≡ loopF r ⌜ F ⌝ (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝
⌜loopF-loop⌝≡ r F k f rewrite ⌜#loop⌝≡ F = refl


tabI : Term → Term
tabI bar = APPLY (loop bar) EMPTY


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
    t #⇛ {--#⇓--} #SUP a f at w  -- For W types
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
               t1 {--#⇓--} #⇛ (#SUP a1 f1) at w
               × t2 {--#⇓--} #⇛ (#SUP a2 f2) at w
               × eqb a1 a2 e b1 b2
               × branch eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))))))))


-- ¬ weq tells us which b's to follow
m2mb : (w : 𝕎·) (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (t u : CTerm)
         → meq₀ eqa eqb w t u
         → ¬ weq₀ eqa eqb w t u
         → branch eqa eqb w t u
branch.branchC (m2mb w eqa eqb t u m nw) with meq₀.meqC₀ m
... | (a1 , f1 , a2 , f2 , e , c1 , c2 , q) =
  a1 , f1 , fst k , a2 , f2 , fst (snd k) , e , c1 , c2 , fst (snd (snd k)) ,
  m2mb w eqa eqb (#APPLY f1 (fst k)) (#APPLY f2 (fst (snd k))) (q (fst k) (fst (snd k)) (fst (snd (snd k)))) (snd (snd (snd k)))
  where
    nj : ¬ ((b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → weq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))
    nj h = nw (weq₀.weqC₀ a1 f1 a2 f2 e c1 c2 h)

    k : Σ CTerm (λ b1 → Σ CTerm (λ b2 → Σ (eqb a1 a2 e b1 b2) (λ eb → ¬ weq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))))
    k with EM {Σ CTerm (λ b1 → Σ CTerm (λ b2 → Σ (eqb a1 a2 e b1 b2) (λ eb → ¬ weq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2))))}
    ... | yes p = p
    ... | no p = ⊥-elim (nj j)
      where
        j : (b1 b2 : CTerm) → eqb a1 a2 e b1 b2 → weq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2)
        j b1 b2 eb with EM {weq₀ eqa eqb w (#APPLY f1 b1) (#APPLY f2 b2)}
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
      → meq₀ (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
      → weq₀ (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u
m2wa i w A B t u cond h with EM {weq₀ (equalInType i w A) (λ a b eqa → equalInType i w (sub0 a B)) w t u}
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


m2w : (kb : K□) (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (t : CTerm)
      → isType i w A
      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
      → ∀𝕎 w (λ w' _ → (p : path i w' A B) → correctPath {i} {w'} {A} {B} t p → isFinPath {i} {w'} {A} {B} p)
      → ∈Type i w (#MT₀ A B) t
      → ∈Type i w (#WT₀ A B) t
m2w kb i w A B t eqta eqtb cond h =
  →equalInType-W₀ i w A B t t eqta eqtb (Mod.∀𝕎-□Func M aw q)
  where
    q : □· w (λ w' _ → meq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    q = equalInType-M₀→ kb i w A B t t h

    aw : ∀𝕎 w (λ w' e' → meq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t
                       → weq₀ (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) w' t t)
    aw w' e' z = m2wa i w' A B t t (cond w' e') z


{--→equalInType-meq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t1 t2 : CTerm)
                    → t1 #⇓ (#SUP a1 f1) at w
                    → t2 #⇓ (#SUP a2 f2) at w
                    → meq eqa eqb w t1 t2
--}


{--
sub-LAMBDA-LAMBDA-loopF≡ : (r : Name) (F : Term) (cF : # F)
                           → sub (loop F) (LAMBDA (LAMBDA (loopF r (shiftUp 0 (shiftUp 0 (shiftUp 0 F))) (VAR 2) (VAR 1) (VAR 0))))
                              ≡ LAMBDA (LAMBDA (loopF r F (loop F) (VAR 1) (VAR 0)))
sub-LAMBDA-LAMBDA-loopF≡ r F cF
  rewrite #subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 (loop F)))))
                  (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 F))))
                  (→#shiftUp 0 {shiftUp 0 (shiftUp 0 (shiftUp 0 F))} (→#shiftUp 0 {shiftUp 0 (shiftUp 0 F)} (→#shiftUp 0 {shiftUp 0 F} (→#shiftUp 0 {F} cF))))
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 7 (ct F cF)
        | #shiftUp 8 (ct F cF)
        | #shiftDown 3 (ct F cF)
        | #shiftDown 11 (ct F cF)
  = refl
--}


sub-LAMBDA-LAMBDA-νloopF≡ : (F : Term) (cF : # F)
                           → sub (loop F) (LAMBDA (LAMBDA (νloopF (shiftUp 0 (shiftUp 0 (shiftUp 0 F))) (VAR 2) (VAR 1) (VAR 0))))
                              ≡ LAMBDA (LAMBDA (νloopF F (loop F) (VAR 1) (VAR 0)))
sub-LAMBDA-LAMBDA-νloopF≡ F cF
  rewrite #subv 3 (shiftUp 0 (shiftNameUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 (loop F))))))
                  (shiftUp 0 (shiftNameUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 F)))))
                  (→#shiftUp 0 {shiftNameUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 F)))} (→#shiftNameUp 0 {shiftUp 0 (shiftUp 0 (shiftUp 0 F))} (→#shiftUp 0 {shiftUp 0 (shiftUp 0 F)} (→#shiftUp 0 {shiftUp 0 F} (→#shiftUp 0 {F} cF)))))
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 8 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftDown 3 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftDown 11 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
  = refl


{--
sub-LAMBDA-loopF≡ : (r : Name) (F k : Term) (cF : # F) (ck : # k)
                    → sub k (LAMBDA (loopF r F (loop F) (VAR 1) (VAR 0)))
                       ≡ LAMBDA (loopF r F (loop F) k (VAR 0))
sub-LAMBDA-loopF≡ r F k cF ck
  rewrite #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 8 (ct F cF)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 1 (ct k ck)
        | #shiftUp 3 (ct k ck)
        | #shiftUp 4 (ct k ck)
        | #shiftUp 5 (ct k ck)
        | #subv 2 k F cF
        | #subv 2 (shiftUp 0 (shiftNameUp 0 k)) F cF
        | #subv 10 k F cF
        | #subv 10 (shiftUp 0 (shiftNameUp 0 k)) F cF
        | #shiftDown 2 (ct F cF)
        | #shiftDown 3 (ct k ck)
        | #shiftDown 5 (ct k ck)
        | #shiftDown 7 (ct k ck)
        | #shiftDown 10 (ct F cF)
  = refl
--}


sub-LAMBDA-νloopF≡ : (F k : Term) (cF : # F) (ck : # k)
                    → sub k (LAMBDA (νloopF F (loop F) (VAR 1) (VAR 0)))
                       ≡ LAMBDA (νloopF F (loop F) k (VAR 0))
sub-LAMBDA-νloopF≡ F k cF ck
  rewrite #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 1 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 3 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 5 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 (shiftNameUp 0 k)) (→#shiftNameUp 0 {shiftNameUp 0 k} (→#shiftNameUp 0 {k} ck)))
        | #shiftUp 0 (ct (shiftNameUp 0 (shiftNameUp 0 k)) (→#shiftNameUp 0 {shiftNameUp 0 k} (→#shiftNameUp 0 {k} ck)))
        | #shiftUp 0 (ct (shiftNameUp 0 (shiftNameUp 0 k)) (→#shiftNameUp 0 {shiftNameUp 0 k} (→#shiftNameUp 0 {k} ck)))
        | #shiftUp 0 (ct (shiftNameUp 0 (shiftNameUp 0 k)) (→#shiftNameUp 0 {shiftNameUp 0 k} (→#shiftNameUp 0 {k} ck)))
        | #shiftUp 0 (ct (shiftNameUp 0 (shiftNameUp 0 k)) (→#shiftNameUp 0 {shiftNameUp 0 k} (→#shiftNameUp 0 {k} ck)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 8 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #subv 2 (shiftNameUp 0 k) (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF)
        | #subv 10 (shiftNameUp 0 (shiftNameUp 0 k)) (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF))
        | #shiftDown 2 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftDown 3 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftDown 5 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftDown 7 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftDown 10 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
  = refl


sub-νloopF≡ : (F k f : Term) (cF : # F) (ck : # k) (cf : # f)
             → sub f (νloopF F (loop F) k (VAR 0))
                ≡ νloopF F (loop F) k f
sub-νloopF≡ F k f cF ck cf
  rewrite #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 3 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 5 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 1 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 3 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 5 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 8 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 0 (ct (shiftNameUp 0 (shiftNameUp 0 f)) (→#shiftNameUp 0 {shiftNameUp 0 f} (→#shiftNameUp 0 {f} cf)))
        | #subv 1 (shiftNameUp 0 f) (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF)
        | #subv 2 (shiftNameUp 0 f) (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck)
        | #subv 4 (shiftNameUp 0 f) (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck)
        | #subv 6 (shiftNameUp 0 f) (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck)
        | #subv 9 (shiftNameUp 0 (shiftNameUp 0 f)) (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF))
        | #shiftDown 1 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftDown 2 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftDown 4 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftDown 6 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftDown 4 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftDown 6 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftDown 9 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
  = refl


loopName+ : (w : 𝕎·) (F k f : Term) → Name
loopName+ w F k f = newChoiceT+ w (νloopFB F (loop F) k f)


loopName : (w : 𝕎·) (F k f : Term) → Name
loopName w F k f = newChoiceT w (νloopFB F (loop F) k f)


#loopName+ : (w : 𝕎·) (F k f : CTerm) → Name
#loopName+ w F k f = newChoiceT+ w ⌜ #νloopFB F (#loop F) k f ⌝


#loopName : (w : 𝕎·) (F k f : CTerm) → Name
#loopName w F k f = newChoiceT w ⌜ #νloopFB F (#loop F) k f ⌝


loop𝕎 : (w : 𝕎·) (F k f : Term) → 𝕎·
loop𝕎 w F k f = startNewChoiceT Res⊤ w (νloopFB F (loop F) k f)


#loop𝕎 : (w : 𝕎·) (F k f : CTerm) → 𝕎·
#loop𝕎 w F k f = startNewChoiceT Res⊤ w ⌜ #νloopFB F (#loop F) k f ⌝


loop𝕎0 : (w : 𝕎·) (F k f : Term) → 𝕎·
loop𝕎0 w F k f = chooseT (loopName w F k f) (loop𝕎 w F k f) N0


#loop𝕎0 : (w : 𝕎·) (F k f : CTerm) → 𝕎·
#loop𝕎0 w F k f = chooseT (#loopName w F k f) (#loop𝕎 w F k f) N0


renn-νloopFB : (w : 𝕎·) (r : Name) (F k f : Term) (ck : # k) (cf : # f) (cF : # F)
               → shiftNameDown 0 (renn 0 (suc r) (νloopFB F (loop F) k f))
                  ≡ loopF r F (loop F) k f
renn-νloopFB w r F k f ck cf cF
  rewrite #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 3 (ct f cf)
        | #shiftUp 5 (ct f cf)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 1 (ct k ck)
        | #shiftUp 3 (ct k ck)
        | #shiftUp 5 (ct k ck)
        | #shiftUp 0 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 4 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 8 (ct (shiftNameUp 0 F) (→#shiftNameUp 0 {F} cF))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 3 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 5 (ct (shiftNameUp 0 f) (→#shiftNameUp 0 {f} cf))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 0 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 1 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 3 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 5 (ct (shiftNameUp 0 k) (→#shiftNameUp 0 {k} ck))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 4 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | #shiftUp 8 (ct (shiftNameUp 1 (shiftNameUp 0 F)) (→#shiftNameUp 1 {shiftNameUp 0 F} (→#shiftNameUp 0 {F} cF)))
        | renn-shiftNameUp 0 (suc r) F
        | renn-shiftNameUp 0 (suc r) f
        | renn-shiftNameUp 0 (suc r) k
        | renn-shiftNameUp 1 (suc (suc r)) (shiftNameUp 0 F)
        | shiftNameDownUp 0 F
        | shiftNameDownUp 0 f
        | shiftNameDownUp 0 k
        | shiftNameDownUp 1 (shiftNameUp 0 F)
  = refl


APPLY-loop⇓! : (F k f : Term) (w : 𝕎·) (cF : # F) (ck : # k) (cf : # f)
                → APPLY2 (loop F) k f ⇓ loopF (loopName w F k f) F (loop F) k f from w to loop𝕎 w F k f
APPLY-loop⇓! F k f w cF ck cf =
  step-⇓-from-to-trans
    {w} {w} {loop𝕎 w F k f}
    {APPLY2 (loop F) k f}
    {APPLY2 (LAMBDA (LAMBDA (νloopF F (loop F) (VAR 1) (VAR 0)))) k f}
    {loopF r F (loop F) k f}
    c1
    (step-⇓-from-to-trans
       {w} {w} {loop𝕎 w F k f}
       {APPLY2 (LAMBDA (LAMBDA (νloopF F (loop F) (VAR 1) (VAR 0)))) k f}
       {APPLY (LAMBDA (νloopF F (loop F) k (VAR 0))) f}
       {loopF r F (loop F) k f}
       c2
       (step-⇓-from-to-trans
          {w} {w} {loop𝕎 w F k f}
          {APPLY (LAMBDA (νloopF F (loop F) k (VAR 0))) f}
          {νloopF F (loop F) k f}
          {loopF r F (loop F) k f}
          c3
          (step→⇓ c4)))
  where
    r+ : Name
    r+ = loopName+ w F k f

    r : Name
    r = loopName w F k f

    c1 : ret (APPLY2 (sub (loop F) (LAMBDA (LAMBDA (νloopF (shiftUp 0 (shiftUp 0 (shiftUp 0 F))) (VAR 2) (VAR 1) (VAR 0))))) k f) w
         ≡ just (APPLY2 (LAMBDA (LAMBDA (νloopF F (loop F) (VAR 1) (VAR 0)))) k f , w)
    c1 rewrite sub-LAMBDA-LAMBDA-νloopF≡ F cF = refl

    c2 : ret (APPLY (sub k (LAMBDA (νloopF F (loop F) (VAR 1) (VAR 0)))) f) w
         ≡ just (APPLY (LAMBDA (νloopF F (loop F) k (VAR 0))) f , w)
    c2 rewrite sub-LAMBDA-νloopF≡ F k cF ck = refl

    c3 : ret (sub f (νloopF F (loop F) k (VAR 0))) w
         ≡ just (νloopF F (loop F) k f , w)
    c3 rewrite sub-νloopF≡ F k f cF ck cf = refl

    c4 : ret (shiftNameDown 0 (renn 0 r+ (νloopFB F (loop F) k f))) (loop𝕎 w F k f)
         ≡ just (loopF r F (loop F) k f , loop𝕎 w F k f)
    c4 = ≡just (≡pair (renn-νloopFB w r F k f ck cf cF) refl)


#APPLY-#loop#⇓1 : (F k f : CTerm) (w : 𝕎·)
                   → #APPLY2 (#loop F) k f #⇓ #loopF (#loopName w F k f) F (#loop F) k f from w to #loop𝕎 w F k f
#APPLY-#loop#⇓1 F k f w =
  APPLY-loop⇓! ⌜ F ⌝ ⌜ k ⌝ ⌜ f ⌝ w (CTerm.closed F) (CTerm.closed k) (CTerm.closed f)


#loopF#⇓#loopA : (r : Name) (F R k f : CTerm) (w : 𝕎·)
                 → #loopF r F R k f #⇓ #loopA r F R k f from w to chooseT r w N0
#loopF#⇓#loopA r F R k f w =
  step-⇓-from-to-trans
    {w} {chooseT r w N0} {chooseT r w N0}
    {loopF r ⌜ F ⌝ ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝}
    {SEQ AX (loopA r ⌜ F ⌝ ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝)}
    {loopA r ⌜ F ⌝ ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝}
    refl
    (SEQ-AX⇓₁from-to {chooseT r w N0} {loopA r ⌜ F ⌝ ⌜ R ⌝ ⌜ k ⌝ ⌜ f ⌝}
                     (CTerm.closed (#loopA r F R k f)))


#APPLY-#loop#⇓2 : (F k f : CTerm) (w : 𝕎·)
                  → #APPLY2 (#loop F) k f #⇓ #loopA (#loopName w F k f) F (#loop F) k f from w to (#loop𝕎0 w F k f)
#APPLY-#loop#⇓2 F k f w =
  ⇓-trans₂ {w} {#loop𝕎 w F k f} {#loop𝕎0 w F k f}
           {APPLY2 (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝}
           {loopF r ⌜ F ⌝ (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝}
           {loopA r ⌜ F ⌝ (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝}
           (#APPLY-#loop#⇓1 F k f w)
           (#loopF#⇓#loopA r F (#loop F) k f (#loop𝕎 w F k f))
  where
    r : Name
    r = #loopName w F k f


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


updBodyL : (name : Name) (a f : Term) → Term
updBodyL name a f = LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))


APPLY-upd⇓ : (r : Name) (w : 𝕎·) (f i : Term) (cf : # f)
             → APPLY (upd r f) i ⇓ updBodyL r i f from w to w
APPLY-upd⇓ r w f i cf = 1 , ≡pair c refl
  where
    c : sub i (updBodyL r (VAR 0) f) ≡ updBodyL r i f
    c rewrite #shiftUp 0 (ct f cf)
            | #subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 i))) f cf
            | #shiftDown 2 (ct f cf)
            | shiftDownUp i 0 = refl


updBody-LET⇓ : (r : Name) (w : 𝕎·) (f : Term) (n : ℕ) (cf : # f)
               → updBodyL r (NUM n) f ⇓ SEQ (updGt r (NUM n)) (APPLY f (NUM n)) from w to w
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


updBodyL⇓APPLY : (cn : cℕ) (r : Name) (i f : Term) (w w' : 𝕎·) (n : ℕ) (cf : # f)
                 → compatible· r w Res⊤
                 → i ⇓ NUM n from w to w'
                 → updBodyL r i f ⇓ APPLY f (NUM n) from w to u𝕎 r n w'
updBodyL⇓APPLY cn r i f w w' n cf compat ci =
  ⇓-trans₂
    {w} {w'} {u𝕎 r n w'}
    {updBodyL r i f}
    {updBodyL r (NUM n) f}
    {APPLY f (NUM n)}
    (LET⇓₁ {w} {w'} {i} {NUM n} {SEQ (updGt r (VAR 0)) (APPLY f (VAR 0))} ci)
    (⇓-trans₂
      {w'} {w'} {u𝕎 r n w'}
      {updBodyL r (NUM n) f}
      {SEQ (updGt r (NUM n)) (APPLY f (NUM n))}
      {APPLY f (NUM n)}
      (updBody-LET⇓ r w' f n cf)
      (SEQ-updtGt⇓ cn r w' n (APPLY f (NUM n)) (CTerm.closed (#APPLY (ct f cf) (#NUM n))) (⊑-compatible· e1 compat)))
  where
    e1 : w ⊑· w'
    e1 = ⇓from-to→⊑ {w} {w'} {i} {NUM n} ci


APPLY-upd⇓2 : (cn : cℕ) (r : Name) (i f : Term) (w w' : 𝕎·) (n : ℕ) (cf : # f)
               → compatible· r w Res⊤
               → i ⇓ NUM n from w to w'
               → APPLY (upd r f) i ⇓ APPLY f (NUM n) from w to u𝕎 r n w'
APPLY-upd⇓2 cn r i f w w' n cf compat ci =
  ⇓-trans₂
    {w} {w} {u𝕎 r n w'}
    {APPLY (upd r f) i}
    {LET i (SEQ (updGt r (VAR 0)) (APPLY f (VAR 0)))}
    {APPLY f (NUM n)}
    (APPLY-upd⇓ r w f i cf)
    (updBodyL⇓APPLY cn r i f w w' n cf compat ci)


#APPLY-#upd⇓2 : (cn : cℕ) (r : Name) (i f : CTerm) (w : 𝕎·) (n : ℕ)
                → compatible· r w Res⊤
                → i #⇛ #NUM n at w
                → Σ 𝕎· (λ w' → #APPLY (#upd r f) i #⇓ #APPLY f (#NUM n) from w to u𝕎 r n w')
#APPLY-#upd⇓2 cn r i f w n compat ci =
  fst ci' , APPLY-upd⇓2 cn r ⌜ i ⌝ ⌜ f ⌝ w (fst ci') n (CTerm.closed f) compat (snd ci')
  where
    ci' : Σ 𝕎· (λ w' → ⌜ i ⌝ ⇓ NUM n from w to w')
    ci' = ⇓→from-to (lower (ci w (⊑-refl· w)))


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


type-preserves-#⇛ : (T : CTerm) → Set(lsuc(L))
type-preserves-#⇛ T =
  (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
  → a₁ #⇛ a₂ at w
  → b₁ #⇛ b₂ at w
  → equalInType i w T a₂ b₂
  → equalInType i w T a₁ b₁


upd∈BAIRE : (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (T f : CTerm)
             → compatible· r w Res⊤
             → type-preserves-#⇛ T
             → isType i w T
             → ∈Type i w (#FUN #NAT T) f
             → ∈Type i w (#FUN #NAT T) (#upd r f)
upd∈BAIRE cn i w r T f compat pres tyT f∈ =
  equalInType-FUN eqTypesNAT tyT aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                        → equalInType i w' T (#APPLY (#upd r f) a₁) (#APPLY (#upd r f) a₂))
    aw1 w1 e1 a₁ a₂ ea = equalInType-local (Mod.∀𝕎-□Func M aw p2)
      where
        p2 : □· w1 (λ w' _ → NATeq w' a₁ a₂)
        p2 = equalInType-NAT→ i w1 a₁ a₂ ea

        aw : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → equalInType i w' T (#APPLY (#upd r f) a₁) (#APPLY (#upd r f) a₂))
        aw w2 e2 (k , c1 , c2) =
          pres i w2 (#APPLY (#upd r f) a₁) (#APPLY f (#NUM k)) (#APPLY (#upd r f) a₂) (#APPLY f (#NUM k))
               (#APPLY-#upd⇛ cn r a₁ f w2 k (⊑-compatible· (⊑-trans· e1 e2) compat) c1)
               (#APPLY-#upd⇛ cn r a₂ f w2 k (⊑-compatible· (⊑-trans· e1 e2) compat) c2)
               (equalInType-FUN→ f∈ w2 (⊑-trans· e1 e2) (#NUM k) (#NUM k) (NUM-equalInType-NAT i w2 k))


APPLY-upd∈NAT : (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (T F f : CTerm)
                 → compatible· r w Res⊤
                 → type-preserves-#⇛ T
                 → isType i w T
                 → ∈Type i w (#FunBar T) F
                 → ∈Type i w (#NAT→T T) f
                 → ∈Type i w #NAT (#APPLY F (#upd r f))
APPLY-upd∈NAT cn i w r T F f compat pres tyT F∈ f∈ =
  F∈' w (⊑-refl· w) (#upd r f) (#upd r f) (upd∈BAIRE cn i w r T f compat pres tyT f∈)
  where
    F∈' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#FUN #NAT T) a₁ a₂ → equalInType i w' #NAT (#APPLY F a₁) (#APPLY F a₂))
    F∈' = equalInType-FUN→ F∈


INL∈IndBarB : (i : ℕ) (w : 𝕎·) (k : ℕ) → ∈Type i w #IndBarB (#INL (#NUM k))
INL∈IndBarB i w k =
  →equalInType-UNION₀!
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #NUM k , #NUM k , inj₁ (#⇛!-refl {w'} {#INL (#NUM k)} ,
                                                    #⇛!-refl {w'} {#INL (#NUM k)} ,
                                                    NUM-equalInType-NAT i w' k)))


-- MOVE to terms3
≡NOWRITEMOD : {a b : Term} → a ≡ b → NOWRITEMOD a ≡ NOWRITEMOD b
≡NOWRITEMOD {a} {b} e rewrite e = refl


≡NOREADMOD : {a b : Term} → a ≡ b → NOREADMOD a ≡ NOREADMOD b
≡NOREADMOD {a} {b} e rewrite e = refl


INR∈IndBarB : (i : ℕ) (w : 𝕎·) → ∈Type i w #IndBarB (#INR #AX)
INR∈IndBarB i w =
  →equalInType-UNION₀!
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #AX , #AX , inj₂ (#⇛!-refl {w'} {#INR #AX} ,
                                            #⇛!-refl {w'} {#INR #AX} ,
                                            →equalInType-TRUE i {w'} {#AX} {#AX})))


sub0-IndBarC≡ : (T a : CTerm) → sub0 a (#IndBarC T) ≡ #DECIDE a #[0]VOID (#[0]shiftUp0 (#NOWRITEMOD T))
sub0-IndBarC≡ T a = CTerm≡ (≡DECIDE x refl (≡NOWRITEMOD y))
  where
    x : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    x rewrite #shiftUp 0 a | #shiftDown 0 a = refl

    y : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) (shiftUp 0 (shiftUp 0 ⌜ T ⌝))) ≡ shiftUp 0 ⌜ T ⌝
    y rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 T | #shiftUp 0 T
            | #subv 1 ⌜ a ⌝ ⌜ T ⌝ (CTerm.closed T) | #shiftDown 1 T = refl


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


#DECIDE-INR⇓ : (w : 𝕎·) (T a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b (#[0]shiftUp0 (#NOWRITEMOD T)) #⇓ #NOWRITEMOD T from w to w
#DECIDE-INR⇓ w T a b = 1 , ≡pair c refl
  where
    c : sub ⌜ a ⌝ (NOWRITEMOD (shiftUp 0 ⌜ T ⌝)) ≡ NOWRITEMOD ⌜ T ⌝
    c rewrite #shiftUp 0 T
            | #shiftUp 0 a
            | #subv 0 ⌜ a ⌝ ⌜ T ⌝ (CTerm.closed T)
            | #shiftDown 0 T = refl


#DECIDE-INR⇛ : (w : 𝕎·) (T a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b (#[0]shiftUp0 (#NOWRITEMOD T)) #⇛! #NOWRITEMOD T at w
#DECIDE-INR⇛ w T a b w1 e1 = lift (#DECIDE-INR⇓ w1 T a b)


#DECIDE⇛INR⇛ : (w : 𝕎·) (T x a : CTerm) (b : CTerm0)
                     → x #⇛ #INR a at w
                     → #DECIDE x b (#[0]shiftUp0 (#NOWRITEMOD T)) #⇛ #NOWRITEMOD T at w
#DECIDE⇛INR⇛ w T x a b comp =
  #⇛-trans
    {w} {#DECIDE x b (#[0]shiftUp0 (#NOWRITEMOD T))} {#DECIDE (#INR a) b (#[0]shiftUp0 (#NOWRITEMOD T))} {#NOWRITEMOD T}
    (DECIDE⇛₁ {w} {⌜ x ⌝} {⌜ #INR a ⌝} {⌜ b ⌝} {⌜ #[0]shiftUp0 (#NOWRITEMOD T) ⌝} comp)
    (#⇛!-#⇛ {w} {#DECIDE (#INR a) b (#[0]shiftUp0 (#NOWRITEMOD T))} {#NOWRITEMOD T} (#DECIDE-INR⇛ w T a b))


#DECIDE⇛INR⇛! : (w : 𝕎·) (T x a : CTerm) (b : CTerm0)
                      → x #⇛! #INR a at w
                      → #DECIDE x b (#[0]shiftUp0 (#NOWRITEMOD T)) #⇛! #NOWRITEMOD T at w
#DECIDE⇛INR⇛! w T x a b comp =
  #⇛!-trans
    {w} {#DECIDE x b (#[0]shiftUp0 (#NOWRITEMOD T))} {#DECIDE (#INR a) b (#[0]shiftUp0 (#NOWRITEMOD T))} {#NOWRITEMOD T}
    (DECIDE⇛!₁ {w} {⌜ x ⌝} {⌜ #INR a ⌝} {⌜ b ⌝} {⌜ #[0]shiftUp0 (#NOWRITEMOD T) ⌝} comp)
    (#DECIDE-INR⇛ w T a b)


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


equalInType-DECIDE-INR→ : (i : ℕ) (w : 𝕎·) (T a b1 b2 : CTerm) (b : CTerm0)
                                → equalInType i w (#DECIDE (#INR a) b (#[0]shiftUp0 (#NOWRITEMOD T))) b1 b2
                                → equalInType i w (#NOWRITEMOD T) b1 b2
equalInType-DECIDE-INR→ i w T a b1 b2 b e =
  equalInType-#⇛ (#DECIDE-INR⇛ w T a b) e


INL→!∈Type-IndBarC : (i : ℕ) (w : 𝕎·) (T x a b : CTerm)
                     → x #⇛! #INL a at w
                     → ¬ ∈Type i w (sub0 x (#IndBarC T)) b
INL→!∈Type-IndBarC i w T x a b comp j rewrite sub0-IndBarC≡ T x =
  ¬equalInType-FALSE j1
  where
    j1 : ∈Type i w #VOID b
    j1 = equalInType-#⇛ (#DECIDE⇛INL-VOID⇛! w x a (#[0]shiftUp0 (#NOWRITEMOD T)) comp) j


type-#⇛!-NUM : (P : ℕ → Set) (T : CTerm) → Set(lsuc(L))
type-#⇛!-NUM P T =
  {i : ℕ} {w : 𝕎·} {a b : CTerm}
  → equalInType i w (#NOWRITEMOD T) a b
  → □· w (λ w' _ → Σ ℕ (λ n → a #⇛! #NUM n at w' × b #⇛! #NUM n at w' × P n))


-- TODO: assume that T computes numbers within a certain range (i.e., using a predicate on numbers)
INR→!∈Type-IndBarC : (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T x a b : CTerm)
                     → type-#⇛!-NUM P T
                     → x #⇛! #INR a at w
                     → ∈Type i w (sub0 x (#IndBarC T)) b
                     → □· w (λ w' _ → Σ ℕ (λ n → b #⇛! #NUM n at w' × P n))
INR→!∈Type-IndBarC i w P T x a b tyn comp j rewrite sub0-IndBarC≡ T x =
  Mod.∀𝕎-□Func M aw (tyn j1)
  where
    j1 : ∈Type i w (#NOWRITEMOD T) b
    j1 = equalInType-#⇛ (#DECIDE⇛INR⇛! w T x a #[0]VOID comp) j

    aw : ∀𝕎 w (λ w' e' → Σ ℕ (λ n → b #⇛! #NUM n at w' × b #⇛! #NUM n at w' × P n)
                        → Σ ℕ (λ n → b #⇛! #NUM n at w' × P n))
    aw w1 e1 (n , c1 , c2 , pn) = n , c1 , pn


∈Type-IndBarB-IndBarC→ : (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T b c : CTerm)
                           → type-#⇛!-NUM P T
                           → ∈Type i w #IndBarB b
                           → ∈Type i w (sub0 b (#IndBarC T)) c
                           → □· w (λ w' _ → Σ CTerm (λ t → b #⇛! #INR t at w') × Σ ℕ (λ n → c #⇛! #NUM n at w' × P n))
∈Type-IndBarB-IndBarC→ i w P T b c tyn b∈ c∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-UNION₀!→ b∈))
  where
    aw : ∀𝕎 w (λ w' e' → UNION₀!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' b b
                        → Mod.□ M w' (↑wPred' (λ w'' _ → Σ CTerm (λ t → b #⇛! #INR t at w'') × Σ ℕ (λ n → c #⇛! #NUM n at w'' × P n)) e'))
    aw w1 e1 (x , y , inj₁ (c1 , c2 , eqi)) = ⊥-elim (INL→!∈Type-IndBarC i w1 T b x c c1 (equalInType-mon c∈ w1 e1))
    aw w1 e1 (x , y , inj₂ (c1 , c2 , eqi)) =
      Mod.∀𝕎-□Func
        M
        (λ w2 e2 (n , cn , pn) z → (x , ∀𝕎-mon e2 c1) , (n , cn , pn))
        (INR→!∈Type-IndBarC i w1 P T b x c tyn c1 (equalInType-mon c∈ w1 e1))


sub-loopI≡ : (r : Name) (R k f i : Term) (cR : # R) (ck : # k) (cf : # f)
             → sub i (loopI r R k f (VAR 0))
                ≡ loopI r R k f i
sub-loopI≡ r R k f i cR ck cf
  rewrite #shiftUp 0 (ct R cR)
        | #shiftUp 0 (ct R cR)
        | #shiftUp 0 (ct R cR)
        | #shiftUp 2 (ct R cR)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 2 (ct k ck)
        | #shiftUp 3 (ct k ck)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 i)))) R cR
        | #subv 4 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 i))))) k ck
        | #subv 4 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 i))))) f cf
        | #shiftDown 3 (ct R cR)
        | #shiftDown 3 (ct k ck)
        | #shiftDown 4 (ct k ck)
        | #shiftDown 4 (ct f cf)
        | #subv 2 i R cR
        | #subv 0 (shiftUp 0 i) k ck
        | #subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 i))) k ck
        | #shiftDown 0 (ct k ck)
        | #shiftDown 2 (ct k ck)
        | #shiftDown 2 (ct R cR)
        | shiftDownUp i 0
  = refl



loopB⇓loopI : (w : 𝕎·) (r : Name) (i : ℕ) (R k f : Term) (cR : # R) (ck : # k) (cf : # f)
              → loopB r (NUM i) R k f ⇓ loopI r R k f (NUM i) from w to w
loopB⇓loopI w r i R k f cR ck cf = 1 , ≡pair c refl
  where
    c : sub (NUM i) (loopI r (shiftUp 0 R) (shiftUp 0 k) (shiftUp 0 f) (VAR 0)) ≡ loopI r R k f (NUM i)
    c rewrite #shiftUp 0 (ct R cR)
            | #shiftUp 0 (ct k ck)
            | sub-loopI≡ r R k f (NUM i) cR ck cf
            | #shiftUp 0 (ct k ck)
            | #shiftUp 0 (ct k ck)
            | #shiftUp 0 (ct k ck)
            | #shiftUp 0 (ct k ck)
            | #shiftUp 2 (ct k ck)
            | #shiftUp 3 (ct k ck)
            | #shiftUp 0 (ct R cR)
            | #shiftUp 0 (ct R cR)
            | #shiftUp 0 (ct R cR)
            | #shiftUp 2 (ct R cR)
            | #shiftUp 0 (ct f cf)
            | #shiftUp 0 (ct f cf)
            | #shiftUp 0 (ct f cf)
            | #shiftUp 0 (ct f cf)
            | #shiftUp 0 (ct f cf)
            | #subv 0 (NUM i) k ck
            | #subv 2 (NUM i) k ck
            | #subv 4 (NUM i) k ck
            | #subv 4 (NUM i) f cf
            | #subv 3 (NUM i) R cR
            | #shiftDown 0 (ct k ck)
            | #shiftDown 2 (ct k ck)
            | #shiftDown 4 (ct k ck)
            | #shiftDown 4 (ct f cf)
            | #shiftDown 3 (ct R cR) = refl


shiftUp00 : (l : CTerm) → shiftUp 0 (shiftUp 0 ⌜ l ⌝) ≡ ⌜ l ⌝
shiftUp00 l rewrite #shiftUp 0 l | #shiftUp 0 l = refl


#loopA#⇓#loopI : (r : Name) (F k f : CTerm) (i : ℕ) (w w' : 𝕎·)
                 → #APPLY F (#upd r f) #⇓ #NUM i from w to w'
                 → #loopA r F (#loop F) k f #⇓ #loopI r (#loop F) k f i from w to w'
#loopA#⇓#loopI r F k f i w w' c =
  ⇓-trans₂
    {w} {w'} {w'} c2
    (loopB⇓loopI
      w' r i (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝
      (CTerm.closed (#loop F)) (CTerm.closed k) (CTerm.closed f))
  where
    c0 : appUpd r ⌜ F ⌝ (shiftUp 0 (shiftUp 0 ⌜ f ⌝)) ⇓ NUM i from w to w'
    c0 rewrite shiftUp00 f = c

    c2 : loopA r ⌜ F ⌝ (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝ ⇓ loopB r (NUM i) (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝ from w to w'
    c2 = LET⇓₁ {w} {w'} {appUpd r ⌜ F ⌝ (shiftUp 0 (shiftUp 0 ⌜ f ⌝))} {NUM i} c0


#APPLY-#loop#⇓3 : (F k f : CTerm) (i : ℕ) (w w' : 𝕎·)
                  → #APPLY F (#upd (#loopName w F k f) f) #⇓ #NUM i from #loop𝕎0 w F k f to w'
                  → #APPLY2 (#loop F) k f #⇓ #loopI (#loopName w F k f) (#loop F) k f i from w to w'
#APPLY-#loop#⇓3 F k f i w w' c =
  ⇓-trans₂
    {w} {#loop𝕎0 w F k f} {w'}
    {APPLY2 (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝}
    {loopA r ⌜ F ⌝ (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝}
    {loopI r (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝ (NUM i)}
    (#APPLY-#loop#⇓2 F k f w)
    (#loopA#⇓#loopI r F k f i (#loop𝕎0 w F k f) w' c)
  where
    r : Name
    r = #loopName w F k f


#loopI⇓#loopII : (w : 𝕎·) (r : Name ) (R k f : CTerm) (i : ℕ)
                 → #loopI r R k f i #⇓ #loopII r R k f i from w to w
#loopI⇓#loopII w r R k f i = 1 , refl


#APPLY-#loop#⇓4₁ : (r : Name) (F k f : CTerm) (i : ℕ) (w : 𝕎·) (m n : ℕ)
                   → getT 0 r w ≡ just (NUM m)
                   → k #⇛ #NUM n at w
                   → m < n
                   → Σ 𝕎· (λ w' → #loopI r (#loop F) k f i #⇓ #ETA (#NUM i) from w to w')
#APPLY-#loop#⇓4₁ r F k f i w m n g ck mn =
  fst c1 ,
  ⇓-trans₂
    {w} {proj₁ c1} {proj₁ c1} c3
    (step→⇓ (IFLT-NUM⇓< m n (fst c1) (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) mn))
  where
    c1 : Σ 𝕎· (λ w' → k #⇓ #NUM n from w to w')
    c1 = #⇓→from-to {w} {k} {#NUM n} (lower (ck w (⊑-refl· w)))

    c0 : steps 1 (get0 r , w) ≡ (NUM m , w)
    c0 rewrite g = refl

    c2 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) k (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to w
    c2 = ⇓-trans₂
           {w} {w} {w} (#loopI⇓#loopII w r (#loop F) k f i)
           (IFLT-NUM-1st⇓ {get0 r} {NUM m} ⌜ k ⌝ (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) (1 , c0))

    c3 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) (#NUM n) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to fst c1
    c3 = ⇓-trans₂ {w} {w} {fst c1} c2 (IFLT-NUM-2nd⇓ m {⌜ k ⌝} {NUM n} (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) (snd c1))


#APPLY-#loop#⇓4₂ : (r : Name) (F k f : CTerm) (i : ℕ) (w : 𝕎·) (m n : ℕ)
                   → getT 0 r w ≡ just (NUM m)
                   → k #⇛! #NUM n at w
                   → m < n
                   → #loopI r (#loop F) k f i #⇓ #ETA (#NUM i) from w to w
#APPLY-#loop#⇓4₂ r F k f i w m n g ck mn =
  ⇓-trans₂
    {w} {w} {w} c3
    (step→⇓ (IFLT-NUM⇓< m n w (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) mn))
  where
    c1 : k #⇓ #NUM n from w to w
    c1 = lower (ck w (⊑-refl· w))

    c0 : steps 1 (get0 r , w) ≡ (NUM m , w)
    c0 rewrite g = refl

    c2 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) k (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to w
    c2 = ⇓-trans₂
           {w} {w} {w} (#loopI⇓#loopII w r (#loop F) k f i)
           (IFLT-NUM-1st⇓ {get0 r} {NUM m} ⌜ k ⌝ (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) (1 , c0))

    c3 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) (#NUM n) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to w
    c3 = ⇓-trans₂ {w} {w} {w} c2 (IFLT-NUM-2nd⇓ m {⌜ k ⌝} {NUM n} (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) c1)


#APPLY-#loop#⇓5₁ : (r : Name) (F k f : CTerm) (i : ℕ) (w : 𝕎·) (m n : ℕ)
                   → getT 0 r w ≡ just (NUM m)
                   → k #⇛ #NUM n at w
                   → ¬ m < n
                   → Σ 𝕎· (λ w' → #loopI r (#loop F) k f i #⇓ #DIGAMMA (#loopR (#loop F) k f) from w to w')
#APPLY-#loop#⇓5₁ r F k f i w m n g ck mn =
  fst c1 ,
  ⇓-trans₂
    {w} {proj₁ c1} {proj₁ c1} c3
    (step→⇓ (IFLT-NUM⇓¬< m n (fst c1) (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) mn))
  where
    c1 : Σ 𝕎· (λ w' → k #⇓ #NUM n from w to w')
    c1 = #⇓→from-to {w} {k} {#NUM n} (lower (ck w (⊑-refl· w)))

    c0 : steps 1 (get0 r , w) ≡ (NUM m , w)
    c0 rewrite g = refl

    c2 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) k (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to w
    c2 = ⇓-trans₂ {w} {w} {w} (#loopI⇓#loopII w r (#loop F) k f i)
           (IFLT-NUM-1st⇓ {get0 r} {NUM m} ⌜ k ⌝ (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) (1 , c0))

    c3 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) (#NUM n) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to fst c1
    c3 = ⇓-trans₂ {w} {w} {fst c1} c2 (IFLT-NUM-2nd⇓ m {⌜ k ⌝} {NUM n} (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) (snd c1))


#APPLY-#loop#⇓5₂ : (r : Name) (F k f : CTerm) (i : ℕ) (w : 𝕎·) (m n : ℕ)
                   → getT 0 r w ≡ just (NUM m)
                   → k #⇛! #NUM n at w
                   → ¬ m < n
                   → #loopI r (#loop F) k f i #⇓ #DIGAMMA (#loopR (#loop F) k f) from w to w
#APPLY-#loop#⇓5₂ r F k f i w m n g ck mn =
  ⇓-trans₂
    {w} {w} {w} c3
    (step→⇓ (IFLT-NUM⇓¬< m n w (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) mn))
  where
    c1 : k #⇓ #NUM n from w to w
    c1 = lower (ck w (⊑-refl· w))

    c0 : steps 1 (get0 r , w) ≡ (NUM m , w)
    c0 rewrite g = refl

    c2 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) k (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to w
    c2 = ⇓-trans₂ {w} {w} {w} (#loopI⇓#loopII w r (#loop F) k f i)
           (IFLT-NUM-1st⇓ {get0 r} {NUM m} ⌜ k ⌝ (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) (1 , c0))

    c3 : #loopI r (#loop F) k f i #⇓ #IFLT (#NUM m) (#NUM n) (#ETA (#NUM i)) (#DIGAMMA (#loopR (#loop F) k f)) from w to w
    c3 = ⇓-trans₂ {w} {w} {w} c2 (IFLT-NUM-2nd⇓ m {⌜ k ⌝} {NUM n} (ETA (NUM i)) (DIGAMMA (loopR (loop ⌜ F ⌝) ⌜ k ⌝ ⌜ f ⌝)) c1)


<⊎¬ : (a b : ℕ) → a < b ⊎ ¬ a < b
<⊎¬ a b with a <? b
... | yes y = inj₁ y
... | no y = inj₂ y


-- MOVE to computation
--#⇓-trans₁ : {w w' : 𝕎·} {a b c : CTerm} → a #⇓ b from w to w' → b #⇓ c at w' → a #⇓ c at w
--#⇓-trans₁ {w} {w'} {a} {b} {c} c₁ c₂ = ⇓-trans₁ {w} {w'} {⌜ a ⌝} {⌜ b ⌝} {⌜ c ⌝} c₁ c₂


-- MOVE to computation
#⇓-trans₂ : {w w' w'' : 𝕎·} {a b c : CTerm} → a #⇓ b from w to w' → b #⇓ c from w' to w'' → a #⇓ c from w to w''
#⇓-trans₂ {w} {w'} {w''} {a} {b} {c} c₁ c₂ = ⇓-trans₂ {w} {w'} {w''} {⌜ a ⌝} {⌜ b ⌝} {⌜ c ⌝} c₁ c₂


abstract

  #APPLY-#loop#⇓4 : (cn : cℕ) (F k f : CTerm) (i n : ℕ) (w w' : 𝕎·)
--                    → compatible· r w Res⊤
                    → k #⇛! #NUM n at w
                    → #APPLY F (#upd (#loopName w F k f) f) #⇓ #NUM i from #loop𝕎0 w F k f to w'
                    → #APPLY2 (#loop F) k f #⇓ #ETA (#NUM i) from w to w'
                       ⊎ #APPLY2 (#loop F) k f #⇓ #DIGAMMA (#loopR (#loop F) k f) from w to w'
  #APPLY-#loop#⇓4 cn F k f i n w w' compk c = d2 (<⊎¬ m n)
    where
      r : Name
      r = #loopName w F k f

      c1 : #APPLY2 (#loop F) k f #⇓ #loopI r (#loop F) k f i from w to w'
      c1 = #APPLY-#loop#⇓3 F k f i w w' c

      w0 : 𝕎·
      w0 = #loop𝕎 w F k f

      e0 : w0 ⊑· w'
      e0 = ⊑-trans· (choose⊑· r w0 (T→ℂ· N0)) (#⇓from-to→⊑ {#loop𝕎0 w F k f} {w'} {#APPLY F (#upd (#loopName w F k f) f)} {#NUM i} c)

      compat : compatible· r w0 Res⊤
      compat = startChoiceCompatible· Res⊤ w r (¬newChoiceT∈dom𝕎 w ⌜ #νloopFB F (#loop F) k f ⌝)

      e1 : w ⊑· w'
      e1 = #⇓from-to→⊑ {w} {w'} {#APPLY2 (#loop F) k f} {#loopI r (#loop F) k f i} c1

      d1 : Σ ℕ (λ j → getT 0 r w' ≡ just (NUM j))
      d1 = lower (cn r w0 compat w' e0)

      m : ℕ
      m = fst d1

      d2 : (m < n ⊎ ¬ m < n)
           → #APPLY2 (#loop F) k f #⇓ #ETA (#NUM i) from w to w'
              ⊎ #APPLY2 (#loop F) k f #⇓ #DIGAMMA (#loopR (#loop F) k f) from w to w'
      d2 (inj₁ x) =
        inj₁ (#⇓-trans₂
                {w} {w'} {w'} {#APPLY2 (#loop F) k f} {#loopI r (#loop F) k f i} {#ETA (#NUM i)}
                c1
                (#APPLY-#loop#⇓4₂ r F k f i w' m n (snd d1) (∀𝕎-mon e1 compk) x))
      d2 (inj₂ x) =
        inj₂ (#⇓-trans₂
                {w} {w'} {w'} {#APPLY2 (#loop F) k f} {#loopI r (#loop F) k f i} {#DIGAMMA (#loopR (#loop F) k f)}
                c1
                (#APPLY-#loop#⇓5₂ r F k f i w' m n (snd d1) (∀𝕎-mon e1 compk) x))


differ⇓APPLY-upd : (cn : comp→∀ℕ) (gc0 : get-choose-ℕ) (F f : Term) (cf : # f)
                   (nnf : ¬Names f) (nnF : ¬Names F) (r r' : Name)
                   (w1 w2 w1' : 𝕎·) (i : ℕ)
                   → compatible· r w1 Res⊤
                   → compatible· r' w1' Res⊤
                   → APPLY F (upd r f) ⇓ NUM i from (chooseT r w1 N0) to w2
                   → Σ 𝕎· (λ w2' → APPLY F (upd r' f) ⇓ NUM i from (chooseT r' w1' N0) to w2' × getT 0 r w2 ≡ getT 0 r' w2')
differ⇓APPLY-upd cn gc0 F f cf nnf nnF r r' w1 w2 w1' i compat1 compat2 comp
  with differ⇓from-to
         gc0 f cf nnf r r' (chooseT r w1 N0) w2 (chooseT r' w1' N0) (APPLY F (upd r f)) (APPLY F (upd r' f)) (NUM i) tt
         (→compatible-chooseT r r w1 N0 Res⊤ compat1)
         (→compatible-chooseT r' r' w1' N0 Res⊤ compat2)
         (cn r w1 0 compat1)
         (differ-APPLY F F (upd r f) (upd r' f) (differ-refl r r' f F nnF) differ-upd)
         (trans (gc0 r w1 0 compat1) (sym (gc0 r' w1' 0 compat2))) comp
... | w2' , .(NUM i) , comp' , differ-NUM .i , gt' = w2' , comp' , gt'


abstract

  #APPLY-#loop#⇓5 : (kb : K□) (can : comp→∀ℕ) (gc0 : get-choose-ℕ) (cn : cℕ) (u : ℕ)
                    (T F k f : CTerm) (n : ℕ) (w : 𝕎·)
                    → (nnf : #¬Names f) (nnF : #¬Names F)
                    → type-preserves-#⇛ T
                    → isType u w T
                    → k #⇛! #NUM n at w
                    → ∈Type u w (#FunBar T) F
                    → ∈Type u w (#FUN #NAT T) f
                    --→ #APPLY F (#upd (#loopName w F k f) f) #⇛ #NUM i at w
                    → Σ ℕ (λ i → #APPLY2 (#loop F) k f #⇛ #ETA (#NUM i) at w)
                       ⊎ #APPLY2 (#loop F) k f #⇛ #DIGAMMA (#loopR (#loop F) k f) at w
  #APPLY-#loop#⇓5 kb can gc0 cn u T F k f n w nnf nnF prest tyt compk F∈ f∈ {--c--} = d2 (<⊎¬ m n)
    where
      r : Name
      r = #loopName w F k f

      c1 : #APPLY2 (#loop F) k f #⇓ #loopF r F (#loop F) k f from w to #loop𝕎 w F k f
      c1 = #APPLY-#loop#⇓1 F k f w

      w0 : 𝕎·
      w0 = #loop𝕎0 w F k f

      e0 : w ⊑· w0
      e0 = ⊑-trans· (#⇓from-to→⊑ {w} {#loop𝕎 w F k f} {#APPLY2 (#loop F) k f} {#loopF r F (#loop F) k f} c1) (choose⊑· r (#loop𝕎 w F k f) (T→ℂ· N0))

      compat : compatible· r (#loop𝕎 w F k f) Res⊤
      compat = startChoiceCompatible· Res⊤ w r (¬newChoiceT∈dom𝕎 w ⌜ #νloopFB F (#loop F) k f ⌝)

      compat0 : compatible· r w0 Res⊤
      compat0 = ⊑-compatible· (choose⊑· r (#loop𝕎 w F k f) (T→ℂ· N0)) compat

      c2 : #loopF r F (#loop F) k f #⇓ #loopA r F (#loop F) k f from (#loop𝕎 w F k f) to w0
      c2 = #loopF#⇓#loopA r F (#loop F) k f (#loop𝕎 w F k f)

      F∈1 : ∈Type u w0 #NAT (#APPLY F (#upd r f))
      F∈1 = equalInType-FUN→
               F∈ w0 e0 (#upd r f) (#upd r f)
               (upd∈BAIRE cn u w0 r T f compat0 prest (eqTypes-mon (uni u) tyt w0 e0) (equalInType-mon f∈ w0 e0))

      F∈2 : NATmem w0 (#APPLY F (#upd r f))
      F∈2 = kb (equalInType-NAT→ u w0 (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) F∈1) w0 (⊑-refl· w0)

      i : ℕ
      i = fst F∈2

      c' : Σ 𝕎· (λ w' → #APPLY F (#upd r f) #⇓ #NUM i from w0 to w')
      c' = ⇓→from-to (lower (fst (snd F∈2) w0 (⊑-refl· w0))) --⇓→from-to (lower (c (chooseT r w N0) (choose⊑· r w (T→ℂ· N0))))

      w' : 𝕎·
      w' = fst c'

      c'' : #APPLY F (#upd r f) #⇓ #NUM i from w0 to w'
      c'' = snd c'

      e' : w0 ⊑· w'
      e' = #⇓from-to→⊑ {w0} {w'} {#APPLY F (#upd r f)} {#NUM i} c''

      c3 : #loopA r F (#loop F) k f #⇓ #loopI r (#loop F) k f i from w0 to w'
      c3 = #loopA#⇓#loopI r F k f i w0 w' c''

      d1 : Σ ℕ (λ j → getT 0 r w' ≡ just (NUM j))
      d1 = lower (cn r w0 compat0 w' e')

      m : ℕ
      m = fst d1

      d2 : (m < n ⊎ ¬ m < n)
           → Σ ℕ (λ i → #APPLY2 (#loop F) k f #⇛ #ETA (#NUM i) at w)
              ⊎ #APPLY2 (#loop F) k f #⇛ #DIGAMMA (#loopR (#loop F) k f) at w
      d2 (inj₁ x) = inj₁ (i , concl ) {--#⇛-trans {w} {#APPLY2 (#loop F) k f} {#loopF r F (#loop F) k f} {#ETA (#NUM i)}
                                    {!!} --(#⇛!→#⇛ {w} {#APPLY2 (#loop F) k f} {#loopF r F (#loop F) k f} c1)
                                    concl)--}
        where
          concl : #APPLY2 (#loop F) k f #⇛ #ETA (#NUM i) at w
-- #loopF r F (#loop F) k f #⇛ #ETA (#NUM i) at w
          concl w1 e1 = lift (#⇓-trans₁ {w1} {#loop𝕎 w1 F k f} {#APPLY2 (#loop F) k f}
                                        {#loopF (#loopName w1 F k f) F (#loop F) k f}
                                        {#ETA (#NUM i)}
                                        (#APPLY-#loop#⇓1 F k f w1)
                                        (#⇓-trans₁ {#loop𝕎 w1 F k f} {#loop𝕎0 w1 F k f}
                                                   {#loopF r' F (#loop F) k f}
                                                   {#loopA r' F (#loop F) k f}
                                                   {#ETA (#NUM i)}
                                                   c2'
                                                   (#⇓-trans₁ {w0'} {w''} {#loopA r' F (#loop F) k f}
                                                              {#loopI r' (#loop F) k f i}
                                                              {#ETA (#NUM i)}
                                                              c3'
                                                              (#⇓from-to→#⇓ {w''} {w''} {#loopI r' (#loop F) k f i}
                                                                             {#ETA (#NUM i)}
                                                                             (#APPLY-#loop#⇓4₂ r' F k f i w'' m n (trans (sym gt') (snd d1)) (∀𝕎-mon (⊑-trans· e1 (⊑-trans· e0' e'')) compk) x)))))
            where
              r' : Name
              r' = #loopName w1 F k f

              w0' : 𝕎·
              w0' = #loop𝕎0 w1 F k f

              e0' : w1 ⊑· w0'
              e0' = ⊑-trans· (#⇓from-to→⊑ {w1} {#loop𝕎 w1 F k f} {#APPLY2 (#loop F) k f} {#loopF r' F (#loop F) k f} (#APPLY-#loop#⇓1 F k f w1)) (choose⊑· r' (#loop𝕎 w1 F k f) (T→ℂ· N0))

              compat' : compatible· r' (#loop𝕎 w1 F k f) Res⊤
              compat' = startChoiceCompatible· Res⊤ w1 r' (¬newChoiceT∈dom𝕎 w1 ⌜ #νloopFB F (#loop F) k f ⌝)

              c2' : #loopF r' F (#loop F) k f #⇓ #loopA r' F (#loop F) k f from (#loop𝕎 w1 F k f) to w0'
              c2' = #loopF#⇓#loopA r' F (#loop F) k f (#loop𝕎 w1 F k f)

              cx : Σ 𝕎· (λ w2' → #APPLY F (#upd r' f) #⇓ #NUM i from w0' to w2' × getT 0 r w' ≡ getT 0 r' w2')
              cx = differ⇓APPLY-upd can gc0 ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed f) nnf nnF r r' (#loop𝕎 w F k f) w' (#loop𝕎 w1 F k f) i compat compat' c''

              w'' : 𝕎·
              w'' = fst cx

              cx' : #APPLY F (#upd r' f) #⇓ #NUM i from w0' to w''
              cx' = fst (snd cx)

              gt' : getT 0 r w' ≡ getT 0 r' w''
              gt' = snd (snd cx)

              c3' : #loopA r' F (#loop F) k f #⇓ #loopI r' (#loop F) k f i from w0' to w''
              c3' = #loopA#⇓#loopI r' F k f i w0' w'' cx'

              e'' : w0' ⊑· w''
              e'' = #⇓from-to→⊑ {w0'} {w''} {#APPLY F (#upd r' f)} {#NUM i} cx'

      d2 (inj₂ x) = inj₂ concl
        where
          concl : #APPLY2 (#loop F) k f #⇛ #DIGAMMA (#loopR (#loop F) k f) at w
          concl w1 e1 = lift (#⇓-trans₁ {w1} {#loop𝕎 w1 F k f} {#APPLY2 (#loop F) k f}
                                        {#loopF (#loopName w1 F k f) F (#loop F) k f}
                                        {#DIGAMMA (#loopR (#loop F) k f)}
                                        (#APPLY-#loop#⇓1 F k f w1)
                                        (#⇓-trans₁ {#loop𝕎 w1 F k f} {#loop𝕎0 w1 F k f}
                                                   {#loopF r' F (#loop F) k f}
                                                   {#loopA r' F (#loop F) k f}
                                                   {#DIGAMMA (#loopR (#loop F) k f)}
                                                   c2'
                                                   (#⇓-trans₁ {w0'} {w''} {#loopA r' F (#loop F) k f}
                                                              {#loopI r' (#loop F) k f i}
                                                              {#DIGAMMA (#loopR (#loop F) k f)}
                                                              c3'
                                                              (#⇓from-to→#⇓ {w''} {w''} {#loopI r' (#loop F) k f i}
                                                                             {#DIGAMMA (#loopR (#loop F) k f)}
                                                                             (#APPLY-#loop#⇓5₂ r' F k f i w'' m n (trans (sym gt') (snd d1)) (∀𝕎-mon (⊑-trans· e1 (⊑-trans· e0' e'')) compk) x)))))
            where
              r' : Name
              r' = #loopName w1 F k f

              w0' : 𝕎·
              w0' = #loop𝕎0 w1 F k f

              e0' : w1 ⊑· w0'
              e0' = ⊑-trans· (#⇓from-to→⊑ {w1} {#loop𝕎 w1 F k f} {#APPLY2 (#loop F) k f} {#loopF r' F (#loop F) k f} (#APPLY-#loop#⇓1 F k f w1)) (choose⊑· r' (#loop𝕎 w1 F k f) (T→ℂ· N0))

              compat' : compatible· r' (#loop𝕎 w1 F k f) Res⊤
              compat' = startChoiceCompatible· Res⊤ w1 r' (¬newChoiceT∈dom𝕎 w1 ⌜ #νloopFB F (#loop F) k f ⌝)

              c2' : #loopF r' F (#loop F) k f #⇓ #loopA r' F (#loop F) k f from (#loop𝕎 w1 F k f) to w0'
              c2' = #loopF#⇓#loopA r' F (#loop F) k f (#loop𝕎 w1 F k f)

              cx : Σ 𝕎· (λ w2' → #APPLY F (#upd r' f) #⇓ #NUM i from w0' to w2' × getT 0 r w' ≡ getT 0 r' w2')
              cx = differ⇓APPLY-upd can gc0 ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed f) nnf nnF r r' (#loop𝕎 w F k f) w' (#loop𝕎 w1 F k f) i compat compat' c''

              w'' : 𝕎·
              w'' = fst cx

              cx' : #APPLY F (#upd r' f) #⇓ #NUM i from w0' to w''
              cx' = fst (snd cx)

              gt' : getT 0 r w' ≡ getT 0 r' w''
              gt' = snd (snd cx)

              c3' : #loopA r' F (#loop F) k f #⇓ #loopI r' (#loop F) k f i from w0' to w''
              c3' = #loopA#⇓#loopI r' F k f i w0' w'' cx'

              e'' : w0' ⊑· w''
              e'' = #⇓from-to→⊑ {w0'} {w''} {#APPLY F (#upd r' f)} {#NUM i} cx'


APPLY-loopR-⇓ : (w1 w2 w3 : 𝕎·) (R k f b : CTerm) (m n : ℕ)
                → b #⇓ #NUM m from w1 to w2
                → k #⇓ #NUM n from w2 to w3
                → #APPLY (#loopR R k f) b #⇓ #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) from w1 to w3
APPLY-loopR-⇓ w1 w2 w3 R k f b m n compb compk =
  ⇓-trans₂
    {w1} {w1} {w3}
    {⌜ #APPLY (#loopR R k f) b ⌝}
    {⌜ #loopRL b R k f ⌝}
    {⌜ #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) ⌝}
    (1 , ≡pair c1 refl)
    (⇓-trans₂
       {w1} {w2} {w3}
       {⌜ #loopRL b R k f ⌝}
       {⌜ #loopRL (#NUM m) R k f ⌝}
       {⌜ #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) ⌝}
       (LET⇓ {⌜ b ⌝} {NUM m} ⌜ #[0]loopRLL (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f) ⌝ compb)
       (⇓-trans₂
          {w2} {w2} {w3}
          {⌜ #loopRL (#NUM m) R k f ⌝}
          {⌜ #loopRLL (#SUC k) (#NUM m) R k f ⌝}
          {⌜ #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) ⌝}
          (1 , ≡pair c2 refl)
          (⇓-trans₂
             {w2} {w3} {w3}
             {⌜ #loopRLL (#SUC k) (#NUM m) R k f ⌝}
             {⌜ #loopRLL (#NUM (suc n)) (#NUM m) R k f ⌝}
             {⌜ #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) ⌝}
             (LET⇓ {⌜ #SUC k ⌝} {NUM (suc n)} ⌜ #[0]loopRLLA (#[0]shiftUp0 (#NUM m)) (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f) ⌝ (⇓NUM→SUC⇓NUM {⌜ k ⌝} {n} {w2} {w3} compk))
             (1 , ≡pair c3 refl))))
-- #loopRL a R l
--APPLY⇓ {w1} {w2}
  where
    c1 : sub ⌜ b ⌝ ⌜ #[0]loopRL (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f) ⌝
         ≡ ⌜ #loopRL b R k f ⌝
    c1 rewrite #shiftUp 0 b
             | #shiftUp 0 b
             | #shiftUp 0 b
             | #shiftUp 0 b
             | #shiftUp 0 R
             | #shiftUp 0 R
             | #shiftUp 0 R
             | #subv 2 ⌜ b ⌝ ⌜ R ⌝ (CTerm.closed R)
             | #shiftDown 2 R
             | #shiftUp 0 k
             | #shiftUp 0 k
             | #shiftUp 0 k
             | #shiftUp 0 k
             | #shiftUp 0 f
             | #shiftUp 0 f
             | #shiftUp 0 f
             | #shiftUp 0 f
             | #subv 1 ⌜ b ⌝ ⌜ k ⌝ (CTerm.closed k)
             | #subv 3 ⌜ b ⌝ ⌜ k ⌝ (CTerm.closed k)
             | #subv 3 ⌜ b ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 3 k
             | #shiftDown 1 k
             | #shiftDown 3 f
             | #shiftDown 0 b = refl

    c2 : sub (NUM m) ⌜ #[0]loopRLL (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f) ⌝
         ≡ ⌜ #loopRLL (#SUC k) (#NUM m) R k f ⌝
    c2 rewrite #shiftUp 0 R
             | #shiftUp 0 R
             | #shiftUp 0 k
             | #shiftUp 0 k
             | #shiftUp 0 k
             | #shiftUp 0 f
             | #shiftUp 0 f
             | #shiftUp 0 f
             | #subv 1 (NUM m) ⌜ R ⌝ (CTerm.closed R)
             | #subv 0 (NUM m) ⌜ k ⌝ (CTerm.closed k)
             | #subv 2 (NUM m) ⌜ k ⌝ (CTerm.closed k)
             | #subv 2 (NUM m) ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 1 R
             | #shiftDown 0 k
             | #shiftDown 2 k
             | #shiftDown 2 f = refl

    c3 : sub (NUM (suc n)) ⌜ #[0]loopRLLA (#[0]shiftUp0 (#NUM m)) (#[0]shiftUp0 R) (#[0]shiftUp0 k) (#[0]shiftUp0 f) ⌝
         ≡ ⌜ #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) ⌝
    c3 rewrite #shiftUp 0 R
             | #shiftUp 0 k
             | #shiftUp 0 k
             | #shiftUp 0 f
             | #shiftUp 0 f
             | #subv 0 (NUM (suc n)) ⌜ R ⌝ (CTerm.closed R)
             | #subv 1 (NUM (suc n)) ⌜ k ⌝ (CTerm.closed k)
             | #subv 1 (NUM (suc n)) ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 0 R
             | #shiftDown 1 k
             | #shiftDown 1 f = refl


{--
APPLY-loopR-⇛ : (w : 𝕎·) (R l b : CTerm) (k : ℕ)
                 → b #⇛ #NUM k at w
                 → #APPLY (#loopR R l) b #⇛! #APPLY R (#APPEND l b) at w
APPLY-loopR-⇛ w R l b k comp w1 e1 = {!!} --lift (APPLY-loopR-⇓ w1 R l b)
--}


{--
upd-SND∈BAIRE : (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (f : CTerm)
                 → compatible· r w Res⊤
                 → ∈Type i w (#LIST #NAT) l
                 → ∈Type i w #BAIRE (#upd r (#SND l))
upd-SND∈BAIRE cn i w r l compat l∈ =
  upd∈BAIRE cn i w r (#SND l) compat (∈LIST→SND i w l l∈)
--}

\end{code}
