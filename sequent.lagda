\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; subst ; cong ; cong₂)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred ; _∸_)
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
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import choiceExt
open import mod --bar --mod
open import encode


module sequent {L  : Level}
               (W  : PossibleWorlds {L})
               (M  : Mod W)
               (C  : Choice)
               (K  : Compatible {L} W C)
               (P  : Progress {L} W C K)
               (G  : GetChoice {L} W C K)
               (X  : ChoiceExt W C)
               (N  : NewChoice W C K G)
               (E  : Extensionality 0ℓ (lsuc(lsuc(L))))
               (EC : Encode)
      where
       --(bar : Bar W) where

open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (predIf≤-sucIf≤ ; subv# ; →#shiftUp ; →#shiftDown ; shiftUp-shiftNameUp)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (shiftNameUp-shiftNameUp)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon ; weq-ext-eq ; meq-ext-eq ; TUNIONeq-ext-eq)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqInType-ext ; □·EqTypes→uniUpTo ; uniUpTo→□·EqTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-mon ; ≡CTerm→equalInType ; ≡CTerm→eqTypes ; equalTypes→equalInType-UNIV ; eqTypesUniv ;
         wPredExtIrr-eqInType ; wPredDepExtIrr-eqInType ; wPredDepExtIrr-eqInType2)


-- ---------------------------------
-- Background stuff


diff : (l k : List Var) → List Var
diff [] k = []
diff (x ∷ l) k with x ∈? k
... | yes p = diff l k
... | no p = x ∷ diff l k


remove : (x : Var) (l : List Var) → List Var
remove x [] = []
remove x (y ∷ l) with x ≟ y
... | yes p = remove x l
... | no p = y ∷ remove x l


diff[] : (l : List Var) → diff l [] ≡ l
diff[] [] = refl
diff[] (x ∷ l) rewrite diff[] l = refl


diff∷ : (l : List Var) (x : Var) (k : List Var) → diff l (x ∷ k) ≡ diff (remove x l) k
diff∷ [] x k = refl
diff∷ (y ∷ l) x k with x ≟ y
... | yes p rewrite p with y ∈? y ∷ k
... |    yes q = diff∷ l y k
... |    no q = ⊥-elim (q (here refl))
diff∷ (y ∷ l) x k | no p with y ∈? x ∷ k
... |    yes q with y ∈? k
... |       yes z = diff∷ l x k
... |       no z = ⊥-elim (z (c q))
  where
    c : y ∈ x ∷ k → y ∈ k
    c (here w) = ⊥-elim (p (sym w))
    c (there w) = w
diff∷ (y ∷ l) x k | no p | no q with y ∈? k
... |       yes z = ⊥-elim (q (there z))
... |       no z rewrite diff∷ l x k = refl


diff-remove≡ : (l : List Var) (x : Var) (k : List Var) → diff (remove x l) k ≡ remove x (diff l k)
diff-remove≡ [] x k = refl
diff-remove≡ (y ∷ l) x k with x ≟ y
... | yes p rewrite p with y ∈? k
... |    yes q = diff-remove≡ l y k
... |    no q with y ≟ y
... |       yes z = diff-remove≡ l y k
... |       no z = ⊥-elim (z refl)
diff-remove≡ (y ∷ l) x k | no p with y ∈? k
... |    yes q = diff-remove≡ l x k
... |    no q with x ≟ y
... |       yes z = ⊥-elim (p z)
... |       no z rewrite diff-remove≡ l x k = refl


fvars-subn0⊆ : (u t : Term) → fvars (subn 0 u t) ⊆ lowerVars (fvars t) ++ fvars u
fvars-subn0⊆ u t rewrite sym (subn≡sub 0 u t) = fvars-sub u t


lowerVarsN : (n : ℕ) (l : List Var) → List Var
lowerVarsN 0 l = l
lowerVarsN (suc n) l = lowerVars (lowerVarsN n l)


lowerVars-lowerVarsN : (n : ℕ) (l : List Var) → lowerVars (lowerVarsN n l) ≡ lowerVarsN n (lowerVars l)
lowerVars-lowerVarsN 0 l = refl
lowerVars-lowerVarsN (suc n) l rewrite lowerVars-lowerVarsN n l = refl


lowerVars⊆lowerVars : (l k : List Var) → l ⊆ k → lowerVars l ⊆ lowerVars k
lowerVars⊆lowerVars l k ss {x} i = →∈lowerVars x k (ss (∈lowerVars→ x l i))


lowerVarsN⊆lowerVarsN : (n : ℕ) (l k : List Var) → l ⊆ k → lowerVarsN n l ⊆ lowerVarsN n k
lowerVarsN⊆lowerVarsN 0 l k ss = ss
lowerVarsN⊆lowerVarsN (suc n) l k ss =
  lowerVars⊆lowerVars
    (lowerVarsN n l)
    (lowerVarsN n k)
    (lowerVarsN⊆lowerVarsN n l k ss)


raiseVars : List Var → List Var
raiseVars l = Data.List.map suc l


lowerVars-raiseVars : (l : List Var) → lowerVars (raiseVars l) ≡ l
lowerVars-raiseVars [] = refl
lowerVars-raiseVars (x ∷ l) rewrite lowerVars-raiseVars l = refl


-- ---------------------------------
-- Sequents

record hypothesis : Set where
  constructor mkHyp
  field
    hyp  : Term


hypotheses : Set
hypotheses = List hypothesis


-- hyps ⊢ ext ∈ concl
record sequent : Set where
  constructor mkSeq
  field
    hyps  : hypotheses
    concl : Term
    ext   : Term


-- H ⊢ a ≡ b ∈ T
mkEqSeq : (H : hypotheses) (a b T : Term) → sequent
mkEqSeq H a b T = mkSeq H (EQ a b T) AX


#hypothesesUpto : List Var → hypotheses → Bool
#hypothesesUpto vs [] = true
#hypothesesUpto vs (mkHyp t ∷ hs) = (fvars t) ⊆? vs ∧ #hypothesesUpto (0 ∷ raiseVars vs) hs


#hypotheses : hypotheses → Set
#hypotheses hs = #hypothesesUpto [] hs ≡ true


-- We don't care about the hypotheses, only the length of the list matters
hdom : hypotheses → List Var
hdom [] = []
hdom (h ∷ hs) = 0 ∷ raiseVars (hdom hs)


record #sequent : Set where
  constructor mk#Seq
  field
    seq    : sequent
    #hyps  : #hypotheses (sequent.hyps seq)
    #concl : #[ hdom (sequent.hyps seq) ] (sequent.concl seq)
    #ext   : #[ hdom (sequent.hyps seq) ] (sequent.ext seq)


record rule : Set where
  constructor mkRule
  field
    premises : List sequent
    goal     : sequent


-- [t,u,v] is the substitution [2\t,1\u,0\v]
Sub : Set
Sub = List CTerm


-- substitute t in hs.
-- E.g., if hs is [ h1 , h2 ] then we replace the 0th var in h1 with t, and the 1st var in h2 with t, etc.
subHyps : (n : ℕ) (t : Term) (hs : hypotheses) → hypotheses
subHyps n t [] = []
subHyps n t (mkHyp h ∷ hs) = mkHyp (subn n t h) ∷ subHyps (suc n) t hs


-- We don't care about the substitution, only its length matters
sdom : Sub → List Var
sdom [] = []
sdom (x ∷ l) = 0 ∷ raiseVars (sdom l)


-- This won't work because of PI types
-- so we're proving this kind of monotonicity above
equalInType≤ : (u : ℕ) → EQT
equalInType≤ u w T a b = {u' : ℕ} (p : u ≤ u') → equalInType u' w T a b


equalTypes≤ : (u : ℕ) → TEQ
equalTypes≤ u w T U = {u' : ℕ} (p : u ≤ u') → equalTypes u' w T U


equalInType≤-mon : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                 → equalInType≤ u w T a b
                 → ∀𝕎 w (λ w' _ → equalInType≤ u w' T a b)
equalInType≤-mon {u} {w} {T} {a} {b} a∈ w' e {u'} u≤ =
  equalInType-mon (a∈ u≤) _ e


equalTypes-mon : {u : ℕ} {w : 𝕎·} {T U : CTerm}
                → equalTypes u w T U
                → ∀𝕎 w (λ w' _ → equalTypes u w' T U)
equalTypes-mon {u} {w} {T} {U} a∈ = eqTypes-mon (uni u) a∈


equalTypes≤-mon : {u : ℕ} {w : 𝕎·} {T U : CTerm}
                → equalTypes≤ u w T U
                → ∀𝕎 w (λ w' _ → equalTypes≤ u w' T U)
equalTypes≤-mon {u} {w} {T} {U} a∈ w' e {u'} u≤ =
  eqTypes-mon (uni u') (a∈ u≤) _ e


≡CTerm→equalInType≤ : {u : ℕ} {w : 𝕎·} {A B a b : CTerm}
                    → A ≡ B
                    → equalInType≤ u w A a b
                    → equalInType≤ u w B a b
≡CTerm→equalInType≤ {u} {w} {A} {B} {a} {b} refl h = h


equalTypes→equalInType≤-UNIV : {n i : ℕ} (p : i < n) {w : 𝕎·} {a b : CTerm}
                              → equalTypes i w a b
                              → equalInType≤ n w (#UNIV i) a b
equalTypes→equalInType≤-UNIV {n} {i} p {w} {a} {b} eqt {n'} n≤ =
  equalTypes→equalInType-UNIV {n'} {i} (≤-trans p n≤) {w} {a} {b} eqt


eqTypes≤Univ : (w : 𝕎·) (n i : ℕ) (p : i < n) → equalTypes≤ n w (#UNIV i) (#UNIV i)
eqTypes≤Univ w n i p {n'} n≤ = eqTypesUniv w n' i (≤-trans p n≤)


-- The 'similarity' relation
data ≡subs : ℕ → 𝕎· → Sub → Sub → hypotheses → Set(lsuc L) where
  ≡subs[] : (i : ℕ) (w : 𝕎·) → ≡subs i w [] [] []
  ≡subs∷ : (i : ℕ) (w : 𝕎·) (t1 t2 : CTerm) (s1 s2 : Sub) (T : Term) (#T : # T) (hs : hypotheses)
           → equalInType i w (ct T #T) t1 t2
           → ≡subs i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs)
           → ≡subs i w (t1 ∷ s1) (t2 ∷ s2) (mkHyp T ∷ hs)


-- The 'eq_hyps' relation
data ≡hyps : ℕ → 𝕎· → Sub → Sub → hypotheses → hypotheses → Set(lsuc L) where
  ≡hyps[] : (i : ℕ) (w : 𝕎·) → ≡hyps i w [] [] [] []
  ≡hyps∷ : (i : ℕ) (w : 𝕎·) (t1 t2 : CTerm) (s1 s2 : Sub)
            (T1 : Term) (#T1 : # T1) (T2 : Term) (#T2 : # T2) (hs1 hs2 : hypotheses)
            → equalTypes i w (ct T1 #T1) (ct T2 #T2)
            → ≡hyps i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs1) (subHyps 0 ⌜ t2 ⌝ hs2)
            → ≡hyps i w (t1 ∷ s1) (t2 ∷ s2) (mkHyp T1 ∷ hs1) (mkHyp T2 ∷ hs2)


≡subs-mon : {i : ℕ} {w1 w2 : 𝕎·} {s1 s2 : Sub} {H : hypotheses}
          → w1 ⊑· w2
          → ≡subs i w1 s1 s2 H
          → ≡subs i w2 s1 s2 H
≡subs-mon {i} {w1} {w2} {.[]} {.[]} {.[]} e (≡subs[] .i .w1) = ≡subs[] i w2
≡subs-mon {i} {w1} {w2} {.(t1 ∷ s1)} {.(t2 ∷ s2)} {.(mkHyp T ∷ hs)} e (≡subs∷ .i .w1 t1 t2 s1 s2 T #T hs x h) =
  ≡subs∷ i w2 t1 t2 s1 s2 T #T hs (equalInType-mon x w2 e) (≡subs-mon e h)


≡hyps-mon : {i : ℕ} {w1 w2 : 𝕎·} {s1 s2 : Sub} {H1 H2 : hypotheses}
          → w1 ⊑· w2
          → ≡hyps i w1 s1 s2 H1 H2
          → ≡hyps i w2 s1 s2 H1 H2
≡hyps-mon {i} {w1} {w2} {.[]} {.[]} {.[]} {.[]} e (≡hyps[] .i .w1) = ≡hyps[] i w2
≡hyps-mon {i} {w1} {w2} {.(t1 ∷ s1)} {.(t2 ∷ s2)} {.(mkHyp T1 ∷ hs1)} {.(mkHyp T2 ∷ hs2)} e (≡hyps∷ .i .w1 t1 t2 s1 s2 T1 #T1 T2 #T2 hs1 hs2 x h) =
  ≡hyps∷ i w2 t1 t2 s1 s2 T1 #T1 T2 #T2 hs1 hs2 (equalTypes-mon x w2 e) (≡hyps-mon e h)


covered : (s : Sub) (t : Term) → Set
covered s t = fvars t ⊆ sdom s


coveredH : (H : hypotheses) (t : Term) → Set
coveredH H t = fvars t ⊆ hdom H


→∈hdom : {x : Var} {H : hypotheses}
       → x < length H
       → x ∈ hdom H
→∈hdom {0} {x₁ ∷ H} i = here refl
→∈hdom {suc x} {x₁ ∷ H} i = there (∈-map⁺ suc (→∈hdom (s≤s-inj i)))


∈raiseVars→ : {x : Var} {l : List Var}
            → suc x ∈ raiseVars l
            → x ∈ l
∈raiseVars→ {x} {l} i with ∈-map⁻ suc i
... | u , v , w rewrite suc-injective w = v


∈hdom→ : {x : Var} {H : hypotheses}
       → x ∈ hdom H
       → x < length H
∈hdom→ {0} {y ∷ H} h = _≤_.s≤s _≤_.z≤n
∈hdom→ {suc x} {y ∷ H} (there h) = _≤_.s≤s (∈hdom→ {x} {H} (∈raiseVars→ h))


subsN : (n : ℕ) (s : Sub) (t : Term) → Term
subsN n [] t = t
subsN n (u ∷ s) t = subn n ⌜ u ⌝ (subsN n s t)


subs : (s : Sub) (t : Term) → Term
subs [] t = t
subs (u ∷ s) t = subn 0 ⌜ u ⌝ (subs s t)


subsN0 : (s : Sub) (t : Term) → subsN 0 s t ≡ subs s t
subsN0 [] t = refl
subsN0 (x ∷ s) t = cong (subn 0 ⌜ x ⌝) (subsN0 s t)


fvars-subs : (s : Sub) (t : Term) → fvars (subs s t) ⊆ lowerVarsN (length s) (fvars t)
fvars-subs [] t = ⊆-refl
fvars-subs (u ∷ s) t = h1
  where
    ind : fvars (subs s t) ⊆ lowerVarsN (length s) (fvars t)
    ind = fvars-subs s t

    h3 : lowerVars (fvars (subs s t)) ⊆ lowerVars (lowerVarsN (length s) (fvars t))
    h3 = lowerVars⊆lowerVars (fvars (subs s t)) (lowerVarsN (length s) (fvars t)) ind

    h2 : lowerVars (fvars (subs s t)) ++ fvars ⌜ u ⌝ ⊆ lowerVars (lowerVarsN (length s) (fvars t))
    h2 rewrite CTerm.closed u | ++[] (lowerVars (fvars (subs s t))) = h3

    h1 : fvars (subn 0 ⌜ u ⌝ (subs s t)) ⊆ lowerVars (lowerVarsN (length s) (fvars t))
    h1 = ⊆-trans (fvars-subn0⊆ ⌜ u ⌝ (subs s t)) h2


lowerVarsN-all-sdom : (s : Sub) → lowerVarsN (length s) (sdom s) ≡ []
lowerVarsN-all-sdom [] = refl
lowerVarsN-all-sdom (x ∷ l)
  rewrite lowerVars-lowerVarsN (length l) (0 ∷ raiseVars (sdom l))
        | lowerVars-raiseVars (sdom l)
  = lowerVarsN-all-sdom l


-- apply the substution s to t - we get a closed term because s 'covers' t
#subs : (s : Sub) (t : Term) (c : covered s t) → CTerm
#subs s t c = ct (subs s t) c'
  where
    ss1 : fvars (subs s t) ⊆ lowerVarsN (length s) (sdom s)
    ss1 = ⊆-trans (fvars-subs s t) (lowerVarsN⊆lowerVarsN (length s) (fvars t) (sdom s) c)

    c' : # subs s t
    c' = ⊆[]→≡[] (⊆-trans ss1 (≡[]→⊆[] (lowerVarsN-all-sdom s)))


sequent_pairwise_true : ℕ → 𝕎· → sequent → Set(lsuc(L))
sequent_pairwise_true i w (mkSeq hyps concl ext) =
  (s1 s2 : Sub) (cc1 : covered s1 concl) (cc2 : covered s2 concl) (ce1 : covered s1 ext) (ce2 : covered s2 ext)
  → ≡subs i w s1 s2 hyps
  → ≡hyps i w s1 s2 hyps hyps
  → equalTypes i w (#subs s1 concl cc1) (#subs s2 concl cc2)
     × equalInType i w (#subs s1 concl cc1) (#subs s1 ext ce1) (#subs s2 ext ce2)


valid : (n : ℕ) (w : 𝕎·) (s : sequent) → Set(lsuc(L))
valid n w s = sequent_pairwise_true n w s


valid≡ : (n : ℕ) (w : 𝕎·) (H : hypotheses) (a b T : Term) → Set(lsuc(L))
valid≡ n w H a b T = sequent_pairwise_true n w (mkEqSeq H a b T)


valid∈ : (n : ℕ) (w : 𝕎·) (H : hypotheses) (a T : Term) → Set(lsuc(L))
valid∈ n w H a T = sequent_pairwise_true n w (mkSeq H T a)


valid∈𝕎 : (n : ℕ) (H : hypotheses) (a T : Term) → Set(lsuc(L))
valid∈𝕎 n H a T = (w : 𝕎·) → valid∈ n w H a T


-- More properties about subs

subs-NAT! : (s : Sub)
          → subs s NAT! ≡ NAT!
subs-NAT! [] = refl
subs-NAT! (x ∷ s) rewrite subs-NAT! s = refl


#subs-NAT! : (s : Sub) (c : covered s NAT!)
           → #subs s NAT! c ≡ #NAT!
#subs-NAT! s c = CTerm≡ (subs-NAT! s)


subs-N0 : (s : Sub)
          → subs s N0 ≡ N0
subs-N0 [] = refl
subs-N0 (x ∷ s) rewrite subs-N0 s = refl


#subs-N0 : (s : Sub) (c : covered s N0)
           → #subs s N0 c ≡ #N0
#subs-N0 s c = CTerm≡ (subs-N0 s)


subs-FALSE : (s : Sub)
           → subs s FALSE ≡ FALSE
subs-FALSE [] = refl
subs-FALSE (x ∷ s) rewrite subs-FALSE s = refl


#subs-FALSE : (s : Sub) (c : covered s FALSE)
            → #subs s FALSE c ≡ #FALSE
#subs-FALSE s c = CTerm≡ (subs-FALSE s)


subs-UNIT : (s : Sub)
           → subs s UNIT ≡ UNIT
subs-UNIT [] = refl
subs-UNIT (x ∷ s) rewrite subs-UNIT s = refl


#subs-UNIT : (s : Sub) (c : covered s UNIT)
            → #subs s UNIT c ≡ #TRUE
#subs-UNIT s c = CTerm≡ (subs-UNIT s)


subs-AX : (s : Sub)
        → subs s AX ≡ AX
subs-AX [] = refl
subs-AX (x ∷ s) rewrite subs-AX s = refl


#subs-AX : (s : Sub) (c : covered s AX)
         → #subs s AX c ≡ #AX
#subs-AX s c = CTerm≡ (subs-AX s)


subs-UNIV : (s : Sub) (i : ℕ)
          → subs s (UNIV i) ≡ UNIV i
subs-UNIV [] i = refl
subs-UNIV (x ∷ s) i rewrite subs-UNIV s i = refl


#subs-UNIV : (s : Sub) (i : ℕ) (c : covered s (UNIV i))
           → #subs s (UNIV i) c ≡ #UNIV i
#subs-UNIV s i c = CTerm≡ (subs-UNIV s i)


covered0 : (s : Sub) (t : Term) → Set
covered0 s t = lowerVars (fvars t) ⊆ sdom s
--covered0 s t = fvars t ⊆ raiseVars (sdom s)


lowerVars⊆[]→ : (l : List Var)
              → lowerVars l ⊆ []
              → l ⊆ [ 0 ]
lowerVars⊆[]→ [] h {x} ()
lowerVars⊆[]→ (0 ∷ l) h {y} (here px) rewrite px = here refl
lowerVars⊆[]→ (suc x ∷ l) h {y} (here px) rewrite px = ⊥-elim (¬∈[] {_} {x} (h {x} (here refl)))
lowerVars⊆[]→ (0 ∷ l) h {y} (there i) = lowerVars⊆[]→ l h {y} i
lowerVars⊆[]→ (suc x ∷ l) h {y} (there i) = lowerVars⊆[]→ l (⊆-trans (xs⊆x∷xs (lowerVars l) x) h) {y} i


lowerVarsN⊆[0] : (l : List Var) (s : Sub)
               → lowerVars l ⊆ sdom s
               → lowerVarsN (length s) l ⊆ [ 0 ]
lowerVarsN⊆[0] l [] h = h1
  where
  h1 : l ⊆ [ 0 ]
  h1 = lowerVars⊆[]→ l h
lowerVarsN⊆[0] l (x ∷ s) h
  rewrite lowerVars-lowerVarsN (length s) l
  = h1
  where
  h3 : lowerVars (raiseVars (sdom s)) ⊆ sdom s
  h3 rewrite lowerVars-raiseVars (sdom s) = ⊆-refl

  h2 : lowerVarsN (length s) (0 ∷ raiseVars (sdom s)) ⊆ [ 0 ]
  h2 = lowerVarsN⊆[0] (0 ∷ (raiseVars (sdom s))) s h3

  h1 : lowerVarsN (length s) (lowerVars l) ⊆ [ 0 ]
  h1 = ⊆-trans (lowerVarsN⊆lowerVarsN (length s) (lowerVars l) (0 ∷ (raiseVars (sdom s))) h) h2


suc-predIf≤-suc : (y : ℕ) → ¬ (suc y ≡ 1) → suc (predIf≤ 1 (suc y)) ≡ suc y
suc-predIf≤-suc y h with suc y ≤? 1
... | yes p = ⊥-elim (h (cong suc (≤-s≤s-≡ 0 y _≤_.z≤n p)))
... | no p = refl


fvars-subn1⊆ : (u t : Term) → fvars (subn 1 u t) ⊆ 0 ∷ lowerVars (fvars t) ++ fvars u
fvars-subn1⊆ u t {x} i
  rewrite sym (subn≡sub 1 u t)
        | fvars-shiftDown≡ 1 (subv 1 (shiftUp 1 u) t)
  with ∈-map⁻ (predIf≤ 1) i
... | 0 , j , z rewrite z = here refl
... | suc y , j , z rewrite z = j2
  where
  j1 : suc y ∈ removeV 1 (fvars t) ++ fvars (shiftUp 1 u)
  j1 = fvars-subv 1 (shiftUp 1 u) t {suc y} j

  j2 : predIf≤ 1 (suc y) ∈ 0 ∷ lowerVars (fvars t) ++ fvars u
  j2 with ∈-++⁻ (removeV 1 (fvars t)) j1
  ... | inj₁ x1 with ∈removeV→ {suc y} {1} {fvars t} x1
  ... | x2 , x3 = there (∈-++⁺ˡ {_} {_} {_} {lowerVars (fvars t)} (→∈lowerVars (predIf≤ 1 (suc y)) (fvars t) (subst (λ x → x ∈ fvars t) (sym (suc-predIf≤-suc y x3)) x2)))
  j2 | inj₂ x2 rewrite fvars-shiftUp≡ 1 u with ∈-map⁻ (sucIf≤ 1) x2
  ... | k , k1 , k2 = subst (λ x → predIf≤ 1 x ∈ 0 ∷ lowerVars (fvars t) ++ fvars u) (sym k2) k3
    where
    k3 : predIf≤ 1 (sucIf≤ 1 k) ∈ 0 ∷ lowerVars (fvars t) ++ fvars u
    k3 rewrite predIf≤-sucIf≤ 1 k = there (∈-++⁺ʳ (lowerVars (fvars t)) k1)


-- generalize
∷⊆ : {v : Var} {l k : List Var}
   → v ∈ k
   → l ⊆ k
   → v ∷ l ⊆ k
∷⊆ {v} {l} {k} i j {x} (here px) rewrite px = i
∷⊆ {v} {l} {k} i j {x} (there z) = j z


fvars-subsN1 : (s : Sub) (t : Term) → fvars (subsN 1 s t) ⊆ 0 ∷ lowerVarsN (length s) (fvars t)
fvars-subsN1 [] t = xs⊆x∷xs (fvars t) 0
fvars-subsN1 (x ∷ s) t = h1
  where
  ind : fvars (subsN 1 s t) ⊆ 0 ∷ lowerVarsN (length s) (fvars t)
  ind = fvars-subsN1 s t

  h3 : lowerVars (fvars (subsN 1 s t))
     ⊆ 0 ∷ lowerVars (lowerVarsN (length s) (fvars t))
  h3 = ⊆-trans (lowerVars⊆lowerVars (fvars (subsN 1 s t)) (0 ∷ lowerVarsN (length s) (fvars t)) ind) there

  h2 : 0 ∷ lowerVars (fvars (subsN 1 s t)) ++ fvars ⌜ x ⌝
     ⊆ 0 ∷ lowerVars (lowerVarsN (length s) (fvars t))
  h2 rewrite CTerm.closed x | ++[] (0 ∷ lowerVars (fvars (subsN 1 s t))) = ∷⊆ (here refl) h3

  h1 : fvars (subn 1 ⌜ x ⌝ (subsN 1 s t)) ⊆ 0 ∷ lowerVars (lowerVarsN (length s) (fvars t))
  h1 = ⊆-trans (fvars-subn1⊆ ⌜ x ⌝ (subsN 1 s t)) h2


#[0]subs : (s : Sub) (t : Term) (c : covered0 s t) → CTerm0
#[0]subs s t c = ct0 (subsN 1 s t) c1
  where
  c2 : fvars (subsN 1 s t) ⊆ [ 0 ]
  c2 = ⊆-trans (fvars-subsN1 s t) (∷⊆ (here refl) (lowerVarsN⊆[0] (fvars t) s c))

  c1 : #[ [ 0 ] ] subsN 1 s t
  c1 = ⊆→⊆? {fvars (subsN 1 s t)} {[ 0 ]} c2


subs-PI : (s : Sub) (a b : Term)
        → subs s (PI a b) ≡ PI (subs s a) (subsN 1 s b)
subs-PI [] a b = refl
subs-PI (x ∷ s) a b
  rewrite subs-PI s a b
        | #shiftUp 0 x = refl


coveredPI₁ : {s : Sub} {a b : Term}
           → covered s (PI a b)
           → covered s a
coveredPI₁ {s} {a} {b} c {x} i = c {x} (∈-++⁺ˡ i)


coveredPI₂ : {s : Sub} {a b : Term}
           → covered s (PI a b)
           → covered0 s b
coveredPI₂ {s} {a} {b} c {x} i = c {x} (∈-++⁺ʳ (fvars a) i)


coveredNATREC₁ : {s : Sub} {a b c : Term}
               → covered s (NATREC a b c)
               → covered s a
coveredNATREC₁ {s} {a} {b} {c} cov {x} i = cov {x} (∈-++⁺ˡ i)


coveredNATREC₂ : {s : Sub} {a b c : Term}
               → covered s (NATREC a b c)
               → covered s b
coveredNATREC₂ {s} {a} {b} {c} cov {x} i = cov {x} (∈-++⁺ʳ (fvars a) (∈-++⁺ˡ i))


coveredNATREC₃ : {s : Sub} {a b c : Term}
               → covered s (NATREC a b c)
               → covered s c
coveredNATREC₃ {s} {a} {b} {c} cov {x} i = cov {x} (∈-++⁺ʳ (fvars a) (∈-++⁺ʳ (fvars b) i))


subs-SUM : (s : Sub) (a b : Term)
        → subs s (SUM a b) ≡ SUM (subs s a) (subsN 1 s b)
subs-SUM [] a b = refl
subs-SUM (x ∷ s) a b
  rewrite subs-SUM s a b
        | #shiftUp 0 x = refl


coveredSUM₁ : {s : Sub} {a b : Term}
           → covered s (SUM a b)
           → covered s a
coveredSUM₁ {s} {a} {b} c {x} i = c {x} (∈-++⁺ˡ i)


coveredSUM₂ : {s : Sub} {a b : Term}
           → covered s (SUM a b)
           → covered0 s b
coveredSUM₂ {s} {a} {b} c {x} i = c {x} (∈-++⁺ʳ (fvars a) i)


covered-FALSE : (s : Sub) → covered s FALSE
covered-FALSE s ()


covered-UNIV : (s : Sub) (i : ℕ) → covered s (UNIV i)
covered-UNIV s i ()


covered-NAT! : (s : Sub) → covered s NAT!
covered-NAT! s ()


covered-AX : (s : Sub) → covered s AX
covered-AX s ()


→coveredEQ : {s : Sub} {a b T : Term}
           → covered s a
           → covered s b
           → covered s T
           → covered s (EQ a b T)
→coveredEQ {s} {a} {b} {T} ca cb cT {x} i with ∈-++⁻ (fvars a) i
... | inj₁ j = ca j
... | inj₂ j with ∈-++⁻ (fvars b) j
... | inj₁ k = cb k
... | inj₂ k = cT k


→coveredSUC : {s : Sub} {a : Term}
            → covered s a
            → covered s (SUC a)
→coveredSUC {s} {a} ca = ca


subs-EQ : (s : Sub) (a b T : Term)
        → subs s (EQ a b T) ≡ EQ (subs s a) (subs s b) (subs s T)
subs-EQ [] a b T = refl
subs-EQ (x ∷ s) a b T
  rewrite subs-EQ s a b T
  = refl


subs-SUC : (s : Sub) (a : Term)
         → subs s (SUC a) ≡ SUC (subs s a)
subs-SUC [] a = refl
subs-SUC (x ∷ s) a
  rewrite subs-SUC s a
  = refl


#subs-SUC : (s : Sub) (a : Term) (c : covered s a)
         → #subs s (SUC a) c ≡ #SUC (#subs s a c)
#subs-SUC s a c = CTerm≡ (subs-SUC s a)


#subs-PI : (s : Sub) (a b : Term) (c : covered s (PI a b)) (ca : covered s a) (cb : covered0 s b)
         → #subs s (PI a b) c ≡ #PI (#subs s a ca) (#[0]subs s b cb)
#subs-PI s a b c ca cb = CTerm≡ (subs-PI s a b)


#subs-PI2 : (s : Sub) (a b : Term) (c : covered s (PI a b))
          → #subs s (PI a b) c ≡ #PI (#subs s a (coveredPI₁ {s} {a} {b} c)) (#[0]subs s b (coveredPI₂ {s} {a} {b} c))
#subs-PI2 s a b c = #subs-PI s a b c (coveredPI₁ {s} {a} {b} c) (coveredPI₂ {s} {a} {b} c)


#subs-SUM : (s : Sub) (a b : Term) (c : covered s (SUM a b)) (ca : covered s a) (cb : covered0 s b)
         → #subs s (SUM a b) c ≡ #SUM (#subs s a ca) (#[0]subs s b cb)
#subs-SUM s a b c ca cb = CTerm≡ (subs-SUM s a b)


#subs-SUM2 : (s : Sub) (a b : Term) (c : covered s (SUM a b))
          → #subs s (SUM a b) c ≡ #SUM (#subs s a (coveredSUM₁ {s} {a} {b} c)) (#[0]subs s b (coveredSUM₂ {s} {a} {b} c))
#subs-SUM2 s a b c = #subs-SUM s a b c (coveredSUM₁ {s} {a} {b} c) (coveredSUM₂ {s} {a} {b} c)


subs-NATREC : (s : Sub) (k z x : Term)
            → subs s (NATREC k z x) ≡ NATREC (subs s k) (subs s z) (subs s x)
subs-NATREC [] k z x = refl
subs-NATREC (a ∷ s) k z x
  rewrite subs-NATREC s k z x
  = refl


#subs-NATREC : (s : Sub) (k z x : Term) (c : covered s (NATREC k z x))
               (ck : covered s k) (cz : covered s z) (cx : covered s x)
             → #subs s (NATREC k z x) c ≡ #NATREC (#subs s k ck) (#subs s z cz) (#subs s x cx)
#subs-NATREC s k z x c ck cz cx = CTerm≡ (subs-NATREC s k z x)


→covered∷ : (a : CTerm) (s : Sub) (t : Term)
          → covered0 s t
          → covered (a ∷ s) t
→covered∷ a s t c {0} i = here refl
→covered∷ a s t c {suc x} i = there (∈-map⁺ suc j)
  where
  j : x ∈ sdom s
  j = c {x} (→∈lowerVars x (fvars t) i)


sdom∷ʳ : (s : Sub) (a : CTerm)
       → sdom (s ∷ʳ a) ≡ 0 ∷ raiseVars (sdom s)
sdom∷ʳ [] a = refl
sdom∷ʳ (x ∷ s) a = cong (λ x → 0 ∷ raiseVars x) (sdom∷ʳ s a)


→covered∷ʳ : (a : CTerm) (s : Sub) (t : Term)
           → covered0 s t
           → covered (s ∷ʳ a) t
→covered∷ʳ a s t c {0} i rewrite sdom∷ʳ s a = here refl
→covered∷ʳ a s t c {suc x} i rewrite sdom∷ʳ s a = there (∈-map⁺ suc j)
  where
  j : x ∈ sdom s
  j = c {x} (→∈lowerVars x (fvars t) i)


≤→predIf≤ : {m n : ℕ} → m ≤ n → predIf≤ n m ≡ m
≤→predIf≤ {0} {n} x = refl
≤→predIf≤ {suc m} {n} x with suc m ≤? n
... | yes p = refl
... | no p = ⊥-elim (p x)


<→predIf≤ : {m n : ℕ} → m ≤ n → predIf≤ m (suc n) ≡ n
<→predIf≤ {m} {n} x with suc n ≤? m
... | yes p = ⊥-elim (<-irrefl refl (≤-trans p x))
... | no p = refl


<→predIf≤2 : {m n : ℕ} → m < n → predIf≤ m n ≡ pred n
<→predIf≤2 {m} {0} x = refl
<→predIf≤2 {m} {suc n} x = <→predIf≤ (s≤s-inj x)


#subn : (n : ℕ) (b a : Term) (ca : # a)
      → subn n b a ≡ a
#subn n b a ca
  rewrite sym (subn≡sub n b a)
        | subv# n (shiftUp n b) a ca
        | #shiftDown n (ct a ca)
  = refl


-- MOVE to util
cong₃ : {ℓ : Level} {A B C D : Set ℓ}
        (f : A → B → C → D) {x y : A} {u v : B} {m n : C}
      → x ≡ y → u ≡ v → m ≡ n → f x u m ≡ f y v n
cong₃ f refl refl refl = refl


-- MOVE to util
cong₄ : {ℓ : Level} {A B C D E : Set ℓ}
        (f : A → B → C → D → E) {x y : A} {u v : B} {m n : C} {a b : D}
      → x ≡ y → u ≡ v → m ≡ n → a ≡ b → f x u m a ≡ f y v n b
cong₄ f refl refl refl refl = refl


≤⇒< : (m n : ℕ) → m ≤ n → ¬ m ≡ n → m < n
≤⇒< m n a b with m≤n⇒m<n∨m≡n a
... | inj₁ c = c
... | inj₂ c = ⊥-elim (b c)


shiftUp-subn : (n m : ℕ) (a b : Term)
             → n ≤ m
             → shiftUp n (subn m a b) ≡ subn (suc m) (shiftUp n a) (shiftUp n b)
-- VAR case
shiftUp-subn n m a (VAR x) len with x ≟ m
shiftUp-subn n m a (VAR x) len | yes p rewrite p with m <? n
shiftUp-subn n m a (VAR x) len | yes p | yes q = ⊥-elim (<-irrefl refl (≤-trans q len))
shiftUp-subn n m a (VAR x) len | yes p | no q with suc m ≟ suc m
shiftUp-subn n m a (VAR x) len | yes p | no q | yes r = refl
shiftUp-subn n m a (VAR x) len | yes p | no q | no r = ⊥-elim (r refl)
shiftUp-subn n m a (VAR x) len | no p with x <? n
shiftUp-subn n m a (VAR x) len | no p | yes q with x ≟ suc m
shiftUp-subn n m a (VAR x) len | no p | yes q | yes r rewrite r = ⊥-elim (<-irrefl refl (≤-trans (_≤_.s≤s (≤-trans len (≤-step ≤-refl))) q))
shiftUp-subn n m a (VAR 0) len | no p | yes q | no r with 0 <? n
... | yes s = refl
... | no s = ⊥-elim (s q)
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r with x <? suc m
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r | yes s with x <? m
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r | yes s | yes i with suc x <? n
... | yes j = refl
... | no j = ⊥-elim (j q)
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r | yes s | no i = ⊥-elim (i (≤-trans (≤-trans (≤-step ≤-refl) q) len))
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r | no s with x <? m
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r | no s | yes i = ⊥-elim (s (≤-trans i (≤-step ≤-refl)))
shiftUp-subn n m a (VAR (suc x)) len | no p | yes q | no r | no s | no i = ⊥-elim (i (≤-trans (≤-trans (≤-step ≤-refl) q) len))
shiftUp-subn n m a (VAR x) len | no p | no q with suc x ≟ suc m
shiftUp-subn n m a (VAR x) len | no p | no q | yes r rewrite sym (suc-injective r) = ⊥-elim (p refl)
shiftUp-subn n m a (VAR x) len | no p | no q | no r with x <? suc m
shiftUp-subn n m a (VAR 0) len | no p | no q | no r | yes s with 0 <? n
... | yes i = ⊥-elim (q i)
... | no i = refl
shiftUp-subn n m a (VAR (suc x)) len | no p | no q | no r | yes s with x <? m
shiftUp-subn n m a (VAR (suc x)) len | no p | no q | no r | yes s | yes i with suc x <? n
... | yes j = ⊥-elim (q j)
... | no j = refl
shiftUp-subn n m a (VAR (suc x)) len | no p | no q | no r | yes s | no i = ⊥-elim (i (s≤s-inj s))
shiftUp-subn n m a (VAR 0) len | no p | no q | no r | no s with 0 <? n
... | yes i = refl
... | no i = ⊥-elim (s (_≤_.s≤s _≤_.z≤n))
shiftUp-subn n m a (VAR (suc x)) len | no p | no q | no r | no s with x <? m
shiftUp-subn n m a (VAR (suc x)) len | no p | no q | no r | no s | yes i = ⊥-elim (s (_≤_.s≤s i))
shiftUp-subn n m a (VAR (suc x)) len | no p | no q | no r | no s | no i with x <? n
... | yes j = ⊥-elim (i (≤-trans j len))
... | no j = refl
--
shiftUp-subn n m a QNAT len = refl
shiftUp-subn n m a (LT b b₁) len =
  cong₂ LT (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (QLT b b₁) len =
  cong₂ QLT (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (NUM x) len = refl
shiftUp-subn n m a (IFLT b b₁ b₂ b₃) len =
  cong₄ IFLT (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len) (shiftUp-subn n m a b₂ len) (shiftUp-subn n m a b₃ len)
shiftUp-subn n m a (IFEQ b b₁ b₂ b₃) len =
  cong₄ IFEQ (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len) (shiftUp-subn n m a b₂ len) (shiftUp-subn n m a b₃ len)
shiftUp-subn n m a (SUC b) len = cong SUC (shiftUp-subn n m a b len)
shiftUp-subn n m a (NATREC b b₁ b₂) len =
  cong₃ NATREC (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len) (shiftUp-subn n m a b₂ len)
shiftUp-subn n m a (PI b b₁) len =
  cong₂ PI (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (LAMBDA b) len =
  cong LAMBDA
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (APPLY b b₁) len =
  cong₂ APPLY (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (FIX b) len = cong FIX (shiftUp-subn n m a b len)
shiftUp-subn n m a (LET b b₁) len =
  cong₂ LET (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (WT b b₁ b₂) len =
  cong₃ WT (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
        (shiftUp-subn n m a b₂ len)
shiftUp-subn n m a (SUP b b₁) len =
  cong₂ SUP (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (WREC b b₁) len =
  cong₂ WREC (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc (suc (suc n))) (suc (suc (suc m))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) b₁ (_≤_.s≤s (_≤_.s≤s (_≤_.s≤s len))))
               (cong (λ z → subn (suc (suc (suc (suc m)))) z (shiftUp (suc (suc (suc n))) b₁))
                     (sym (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUpUp 0 n a _≤_.z≤n))
                                                          (shiftUpUp 0 (suc n) (shiftUp 0 a) _≤_.z≤n)))
                                 (shiftUpUp 0 (suc (suc n)) (shiftUp 0 (shiftUp 0 a)) _≤_.z≤n)))))
shiftUp-subn n m a (MT b b₁ b₂) len =
  cong₃ MT (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
        (shiftUp-subn n m a b₂ len)
shiftUp-subn n m a (SUM b b₁) len =
  cong₂ SUM (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (PAIR b b₁) len =
  cong₂ PAIR (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (SPREAD b b₁) len =
  cong₂ SPREAD (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc (suc n)) (suc (suc m)) (shiftUp 0 (shiftUp 0 a)) b₁ (_≤_.s≤s (_≤_.s≤s len)))
               (cong (λ z → subn (suc (suc (suc m))) z (shiftUp (suc (suc n)) b₁))
                     (sym (trans (cong (shiftUp 0) (shiftUpUp 0 n a _≤_.z≤n))
                                 (shiftUpUp 0 (suc n) (shiftUp 0 a) _≤_.z≤n)))))
shiftUp-subn n m a (SET b b₁) len =
  cong₂ SET (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (TUNION b b₁) len =
  cong₂ TUNION (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (ISECT b b₁) len =
  cong₂ ISECT (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (UNION b b₁) len =
  cong₂ UNION (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (INL b) len = cong INL (shiftUp-subn n m a b len)
shiftUp-subn n m a (INR b) len = cong INR (shiftUp-subn n m a b len)
shiftUp-subn n m a (DECIDE b b₁ b₂) len =
  cong₃ DECIDE (shiftUp-subn n m a b len)
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
        (trans (shiftUp-subn (suc n) (suc m) (shiftUp 0 a) b₂ (_≤_.s≤s len))
               (cong (λ z → subn (suc (suc m)) z (shiftUp (suc n) b₂)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subn n m a (EQ b b₁ b₂) len =
  cong₃ EQ (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len) (shiftUp-subn n m a b₂ len)
shiftUp-subn n m a AX len = refl
shiftUp-subn n m a FREE len = refl
shiftUp-subn n m a (CS x) len = refl
shiftUp-subn n m a (NAME x) len = refl
shiftUp-subn n m a (FRESH b) len =
  cong FRESH (trans (shiftUp-subn n m (shiftNameUp 0 a) b len)
                    (cong (λ z → subn (suc m) z (shiftUp n b)) (shiftUp-shiftNameUp n 0 a)))
shiftUp-subn n m a (CHOOSE b b₁) len =
  cong₂ CHOOSE (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a (LOAD b) len = refl
shiftUp-subn n m a (MSEQ x) len = refl
shiftUp-subn n m a (MAPP x b) len = cong (λ z → MAPP x z) (shiftUp-subn n m a b len)
shiftUp-subn n m a NOWRITE len = refl
shiftUp-subn n m a NOREAD len = refl
shiftUp-subn n m a (SUBSING b) len = cong SUBSING (shiftUp-subn n m a b len)
shiftUp-subn n m a (DUM b) len = cong DUM (shiftUp-subn n m a b len)
shiftUp-subn n m a (FFDEFS b b₁) len =
  cong₂ FFDEFS (shiftUp-subn n m a b len) (shiftUp-subn n m a b₁ len)
shiftUp-subn n m a PURE len = refl
shiftUp-subn n m a NOSEQ len = refl
shiftUp-subn n m a NOENC len = refl
shiftUp-subn n m a (TERM b) len = cong TERM (shiftUp-subn n m a b len)
shiftUp-subn n m a (ENC b) len = refl
shiftUp-subn n m a (UNIV x) len = refl
shiftUp-subn n m a (LIFT b) len = cong LIFT (shiftUp-subn n m a b len)
shiftUp-subn n m a (LOWER b) len = cong LOWER (shiftUp-subn n m a b len)
shiftUp-subn n m a (SHRINK b) len = cong SHRINK (shiftUp-subn n m a b len)


subn-shiftNameUp : (n m : ℕ) (a b : Term)
                 → subn m (shiftNameUp n a) (shiftNameUp n b)
                 ≡ shiftNameUp n (subn m a b)
subn-shiftNameUp n m a (VAR x) with x ≟ m
... | yes p rewrite p = refl
... | no p = refl
subn-shiftNameUp n m a QNAT = refl
subn-shiftNameUp n m a (LT b b₁) =
  cong₂ LT (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (QLT b b₁) =
  cong₂ QLT (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (NUM x) = refl
subn-shiftNameUp n m a (IFLT b b₁ b₂ b₃) =
  cong₄ IFLT (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
    (subn-shiftNameUp n m a b₂) (subn-shiftNameUp n m a b₃)
subn-shiftNameUp n m a (IFEQ b b₁ b₂ b₃) =
  cong₄ IFEQ (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
    (subn-shiftNameUp n m a b₂) (subn-shiftNameUp n m a b₃)
subn-shiftNameUp n m a (SUC b) = cong SUC (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (NATREC b b₁ b₂) =
  cong₃ NATREC (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁) (subn-shiftNameUp n m a b₂)
subn-shiftNameUp n m a (PI b b₁) =
  cong₂ PI (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
subn-shiftNameUp n m a (LAMBDA b) =
  cong LAMBDA
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b))
subn-shiftNameUp n m a (APPLY b b₁) =
  cong₂ APPLY (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (FIX b) = cong FIX (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (LET b b₁) =
  cong₂ LET (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
subn-shiftNameUp n m a (WT b b₁ b₂) =
  cong₃ WT (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
    (subn-shiftNameUp n m a b₂)
subn-shiftNameUp n m a (SUP b b₁) =
  cong₂ SUP (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (WREC b b₁) =
  cong₂ WREC (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc (suc (suc m))) z (shiftNameUp n b₁))
                 (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUp-shiftNameUp 0 n a))
                                                 (shiftUp-shiftNameUp 0 n (shiftUp 0 a))))
                        (shiftUp-shiftNameUp 0 n (shiftUp 0 (shiftUp 0 a)))))
           (subn-shiftNameUp n (suc (suc (suc m))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) b₁))
subn-shiftNameUp n m a (MT b b₁ b₂) =
  cong₃ MT (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
    (subn-shiftNameUp n m a b₂)
subn-shiftNameUp n m a (SUM b b₁) =
  cong₂ SUM (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
subn-shiftNameUp n m a (PAIR b b₁) =
  cong₂ PAIR (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (SPREAD b b₁) =
  cong₂ SPREAD (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc (suc m)) z (shiftNameUp n b₁))
                 (trans (cong (shiftUp 0) (shiftUp-shiftNameUp 0 n a))
                       (shiftUp-shiftNameUp 0 n (shiftUp 0 a))))
           (subn-shiftNameUp n (suc (suc m)) (shiftUp 0 (shiftUp 0 a)) b₁))
subn-shiftNameUp n m a (SET b b₁) =
  cong₂ SET (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
subn-shiftNameUp n m a (TUNION b b₁) =
  cong₂ TUNION (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
subn-shiftNameUp n m a (ISECT b b₁) =
  cong₂ ISECT (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (UNION b b₁) =
  cong₂ UNION (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (INL b) = cong INL (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (INR b) = cong INR (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (DECIDE b b₁ b₂) =
  cong₃ DECIDE (subn-shiftNameUp n m a b)
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₁)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₁))
    (trans (cong (λ z → subn (suc m) z (shiftNameUp n b₂)) (shiftUp-shiftNameUp 0 n a))
           (subn-shiftNameUp n (suc m) (shiftUp 0 a) b₂))
subn-shiftNameUp n m a (EQ b b₁ b₂) =
  cong₃ EQ (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁) (subn-shiftNameUp n m a b₂)
subn-shiftNameUp n m a AX = refl
subn-shiftNameUp n m a FREE = refl
subn-shiftNameUp n m a (CS x) = refl
subn-shiftNameUp n m a (NAME x) = refl
subn-shiftNameUp n m a (FRESH b) =
  cong FRESH (trans (cong (λ z → subn m z (shiftNameUp (suc n) b)) (shiftNameUp-shiftNameUp {0} {n} {a} _≤_.z≤n))
                    (subn-shiftNameUp (suc n) m (shiftNameUp 0 a) b))
subn-shiftNameUp n m a (CHOOSE b b₁) =
  cong₂ CHOOSE (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a (LOAD b) = refl
subn-shiftNameUp n m a (MSEQ x) = refl
subn-shiftNameUp n m a (MAPP x b) = cong (MAPP x) (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a NOWRITE = refl
subn-shiftNameUp n m a NOREAD = refl
subn-shiftNameUp n m a (SUBSING b) = cong SUBSING (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (DUM b) = cong DUM (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (FFDEFS b b₁) =
  cong₂ FFDEFS (subn-shiftNameUp n m a b) (subn-shiftNameUp n m a b₁)
subn-shiftNameUp n m a PURE = refl
subn-shiftNameUp n m a NOSEQ = refl
subn-shiftNameUp n m a NOENC = refl
subn-shiftNameUp n m a (TERM b) = cong TERM (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (ENC b) = refl
subn-shiftNameUp n m a (UNIV x) = refl
subn-shiftNameUp n m a (LIFT b) = cong LIFT (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (LOWER b) = cong LOWER (subn-shiftNameUp n m a b)
subn-shiftNameUp n m a (SHRINK b) = cong SHRINK (subn-shiftNameUp n m a b)


subn-subn2 : (n m : ℕ) (ltn : m ≤ n) (a b t : Term) (ca : # a)
           → subn m a (subn (suc n) b t) ≡ subn n (subn m a b) (subn m a t)
-- VAR case
subn-subn2 n m ltn a b (VAR x) ca with x ≟ suc n | x ≟ m
subn-subn2 n m ltn a b (VAR x) ca | yes p | yes q rewrite q | p = ⊥-elim (<-irrefl refl ltn)
subn-subn2 n m ltn a b (VAR x) ca | yes p | no  q rewrite p | <→predIf≤ ltn with n ≟ n
... | yes r = refl --rewrite #subn m a b cb = refl
... | no  r = ⊥-elim (r refl)
subn-subn2 n m ltn a b (VAR x) ca | no  p | yes q
  rewrite q | ≤→predIf≤ {m} {suc n} (≤-trans ltn (<⇒≤ ≤-refl))
  with m ≟ m
... | yes r rewrite #subn n (subn m a b) a ca = refl
... | no  r = ⊥-elim (r refl)
subn-subn2 n m ltn a b (VAR 0) ca | no  p | no  q with 0 ≟ m | 0 ≟ n
... | yes r | yes s rewrite sym r | sym s = ⊥-elim (q refl)
... | yes r | no  s rewrite sym r = ⊥-elim (q refl)
... | no  r | yes s rewrite sym s | n≤0⇒n≡0 {m} ltn  = ⊥-elim (q refl)
... | no  r | no  s = refl
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q with suc x ≤? suc n | suc x ≤? m
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q | yes r | yes s with suc x ≟ m | suc x ≟ n
... | yes z | yes w rewrite sym z | sym w = ⊥-elim (q refl)
... | yes z | no  w rewrite sym z = ⊥-elim (q refl)
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q | yes r | yes s | no  z | yes w
  rewrite sym w with x <? m
... | yes y = ⊥-elim (<-irrefl refl (<-transˡ (≤⇒< _ _ y q) ltn))
... | no  y = ⊥-elim (y s)
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q | yes r | yes s | no  z | no  w
  with suc x ≤? m | suc x ≤? n
... | yes i | yes j = refl
... | yes i | no  j = ⊥-elim (j (s≤s-inj (≤⇒< _ _ r p)))
... | no  i | yes j = ⊥-elim (i s)
... | no  i | no  j = refl
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q | yes r | no  s with suc x ≟ m
... | yes y = ⊥-elim (q y)
... | no  y with suc x ≤? m
... | yes z = ⊥-elim (s z)
... | no  z with x ≟ n
... | yes w rewrite w = ⊥-elim (p refl)
... | no  w rewrite ≤→predIf≤ {x} {n} (s≤s-inj r) = refl
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q | no  r | yes s with x ≟ m
... | yes y rewrite y = ⊥-elim (<-irrefl refl s)
... | no  y with x ≟ n
... | yes z rewrite z = ⊥-elim (r ≤-refl)
... | no  z with suc x ≟ n
... | yes w rewrite sym w = ⊥-elim (r (<⇒≤ ≤-refl))
... | no  w with suc x ≤? n
... | yes i = ⊥-elim (r (_≤_.s≤s (<⇒≤ (≤⇒< _ _ (≤-trans (<⇒≤ ≤-refl) i) z))))
... | no  i rewrite ≤→predIf≤ {x} {m} (≤-trans (<⇒≤ ≤-refl) s) = refl
subn-subn2 n m ltn a b (VAR (suc x)) ca | no  p | no  q | no  r | no  s with x ≟ m
... | yes y rewrite y = ⊥-elim (r (_≤_.s≤s ltn))
... | no  y with x ≟ n
... | yes z rewrite z = ⊥-elim (r ≤-refl)
... | no  z rewrite <→predIf≤2 {m} {x} (≤⇒< _ _ (≮⇒≥ s) (λ i → y (sym i)))
                  | <→predIf≤2 {n} {x} (≤⇒< _ _ (≤-trans (<⇒≤ ≤-refl) (≮⇒≥ r)) (λ i → z (sym i))) = refl
--subn-subn2 n m ltn a b (VAR x) ca = {!!}
--
subn-subn2 n m ltn a b QNAT ca = refl
subn-subn2 n m ltn a b (LT t t₁) ca =
  cong₂ LT (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (QLT t t₁) ca =
  cong₂ QLT (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (NUM x) ca = refl
subn-subn2 n m ltn a b (IFLT t t₁ t₂ t₃) ca =
  cong₄ IFLT (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
    (subn-subn2 n m ltn a b t₂ ca) (subn-subn2 n m ltn a b t₃ ca)
subn-subn2 n m ltn a b (IFEQ t t₁ t₂ t₃) ca =
  cong₄ IFEQ (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
    (subn-subn2 n m ltn a b t₂ ca) (subn-subn2 n m ltn a b t₃ ca)
subn-subn2 n m ltn a b (SUC t) ca = cong SUC (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (NATREC t t₁ t₂) ca =
  cong₃ NATREC (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
    (subn-subn2 n m ltn a b t₂ ca)
subn-subn2 n m ltn a b (PI t t₁) ca =
  cong₂ PI (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (LAMBDA t) ca =
  cong LAMBDA
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (APPLY t t₁) ca =
  cong₂ APPLY (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (FIX t) ca = cong FIX (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (LET t t₁) ca =
  cong₂ LET (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (WT t t₁ t₂) ca =
  cong₃ WT (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
    (subn-subn2 n m ltn a b t₂ ca)
subn-subn2 n m ltn a b (SUP t t₁) ca =
  cong₂ SUP (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (WREC t t₁) ca =
  cong₂ WREC (subn-subn2 n m ltn a b t ca)
    (trans
       (subn-subn2 (suc (suc (suc n))) (suc (suc (suc m))) (_≤_.s≤s (_≤_.s≤s (_≤_.s≤s ltn))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b))) t₁ (→#shiftUp 0 {shiftUp 0 (shiftUp 0 a)} (→#shiftUp 0 {shiftUp 0 a} (→#shiftUp 0 {a} ca))))
       (cong
          (λ z → subn (suc (suc (suc n))) z (subn (suc (suc (suc m))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) t₁))
          (sym (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUp-subn 0 m a b _≤_.z≤n))
                                               (shiftUp-subn 0 (suc m) (shiftUp 0 a) (shiftUp 0 b) _≤_.z≤n)))
                      (shiftUp-subn 0 (suc (suc m)) (shiftUp 0 (shiftUp 0 a)) (shiftUp 0 (shiftUp 0 b)) _≤_.z≤n)))))
subn-subn2 n m ltn a b (MT t t₁ t₂) ca =
  cong₃ MT (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
    (subn-subn2 n m ltn a b t₂ ca)
subn-subn2 n m ltn a b (SUM t t₁) ca =
  cong₂ SUM (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (PAIR t t₁) ca =
  cong₂ PAIR (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (SPREAD t t₁) ca =
  cong₂ SPREAD (subn-subn2 n m ltn a b t ca)
    (trans
       (subn-subn2 (suc (suc n)) (suc (suc m)) (_≤_.s≤s (_≤_.s≤s ltn)) (shiftUp 0 (shiftUp 0 a)) (shiftUp 0 (shiftUp 0 b)) t₁ (→#shiftUp 0 {shiftUp 0 a} (→#shiftUp 0 {a} ca)))
       (cong (λ z → subn (suc (suc n)) z (subn (suc (suc m)) (shiftUp 0 (shiftUp 0 a)) t₁))
             (sym (trans (cong (shiftUp 0) (shiftUp-subn 0 m a b _≤_.z≤n))
                         (shiftUp-subn 0 (suc m) (shiftUp 0 a) (shiftUp 0 b) _≤_.z≤n)))))
subn-subn2 n m ltn a b (SET t t₁) ca =
  cong₂ SET (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (TUNION t t₁) ca =
  cong₂ TUNION (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (ISECT t t₁) ca =
  cong₂ ISECT (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (UNION t t₁) ca =
  cong₂ UNION (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (INL t) ca = cong INL (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (INR t) ca = cong INR (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (DECIDE t t₁ t₂) ca =
  cong₃ DECIDE (subn-subn2 n m ltn a b t ca)
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₁))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
    (trans (subn-subn2 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₂ (→#shiftUp 0 {a} ca))
           (cong (λ z → subn (suc n) z (subn (suc m) (shiftUp 0 a) t₂))
                 (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn2 n m ltn a b (EQ t t₁ t₂) ca =
  cong₃ EQ (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
    (subn-subn2 n m ltn a b t₂ ca)
subn-subn2 n m ltn a b AX ca = refl
subn-subn2 n m ltn a b FREE ca = refl
subn-subn2 n m ltn a b (CS x) ca = refl
subn-subn2 n m ltn a b (NAME x) ca = refl
subn-subn2 n m ltn a b (FRESH t) ca =
  cong FRESH (trans (subn-subn2 n m ltn (shiftNameUp 0 a) (shiftNameUp 0 b) t (→#shiftNameUp 0 {a} ca))
    (cong (λ z → subn n z (subn m (shiftNameUp 0 a) t)) (subn-shiftNameUp 0 m a b)))
subn-subn2 n m ltn a b (CHOOSE t t₁) ca =
  cong₂ CHOOSE (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b (LOAD t) ca = refl
subn-subn2 n m ltn a b (MSEQ x) ca = refl
subn-subn2 n m ltn a b (MAPP x t) ca = cong (MAPP x) (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b NOWRITE ca = refl
subn-subn2 n m ltn a b NOREAD ca = refl
subn-subn2 n m ltn a b (SUBSING t) ca = cong SUBSING (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (DUM t) ca = cong DUM (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (FFDEFS t t₁) ca =
  cong₂ FFDEFS (subn-subn2 n m ltn a b t ca) (subn-subn2 n m ltn a b t₁ ca)
subn-subn2 n m ltn a b PURE ca = refl
subn-subn2 n m ltn a b NOSEQ ca = refl
subn-subn2 n m ltn a b NOENC ca = refl
subn-subn2 n m ltn a b (TERM t) ca = cong TERM (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (ENC t) ca = refl
subn-subn2 n m ltn a b (UNIV x) ca = refl
subn-subn2 n m ltn a b (LIFT t) ca = cong LIFT (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (LOWER t) ca = cong LOWER (subn-subn2 n m ltn a b t ca)
subn-subn2 n m ltn a b (SHRINK t) ca = cong SHRINK (subn-subn2 n m ltn a b t ca)


subn-subn : (n : ℕ) (a b t : Term) (ca : # a) (cb : # b)
          → subn n a (subn (suc n) b t) ≡ subn n b (subn n a t)
subn-subn n a b t ca cb =
  trans (subn-subn2 n n ≤-refl a b t ca)
        (cong (λ z → subn n z (subn n a t)) (#subn n a b cb))


subn-subsN1 : (a : CTerm) (s : Sub) (t : Term)
            → subn 0 ⌜ a ⌝ (subsN 1 s t) ≡ subs (s ∷ʳ a) t
subn-subsN1 a [] t = refl
subn-subsN1 a (x ∷ s) t =
  trans
    (subn-subn 0 ⌜ a ⌝ ⌜ x ⌝ (subsN 1 s t) (CTerm.closed a) (CTerm.closed x))
    (cong (subn 0 ⌜ x ⌝) (subn-subsN1 a s t))


sub-subsN1 : (a : CTerm) (s : Sub) (t : Term)
           → sub ⌜ a ⌝ (subsN 1 s t) ≡ subs (s ∷ʳ a) t
sub-subsN1 a s t rewrite sub≡subn ⌜ a ⌝ (subsN 1 s t) = subn-subsN1 a s t


sub0-#[0]subs : (a : CTerm) (s : Sub) (t : Term) (c : covered0 s t)
              → sub0 a (#[0]subs s t c) ≡ #subs (s ∷ʳ a) t (→covered∷ʳ a s t c)
sub0-#[0]subs a s t c = CTerm≡ (sub-subsN1 a s t)


covered[]→# : {F : Term}
            → covered [] F
            → # F
covered[]→# {F} c = ⊆[]→≡[] c


subHyps∷ʳ : (n : ℕ) (t F : Term) (hs : hypotheses)
          → subHyps n t (hs ∷ʳ mkHyp F) ≡ subHyps n t hs ∷ʳ mkHyp (subn (n + length hs) t F)
subHyps∷ʳ n t F [] rewrite +0 n = refl
subHyps∷ʳ n t F (mkHyp h ∷ hs) rewrite +-suc n (length hs) =
  cong (λ z → mkHyp (subn n t h) ∷ z)
       (subHyps∷ʳ (suc n) t F hs)


length-subHyps : (n : ℕ) (t : Term) (H : hypotheses)
               → length (subHyps n t H) ≡ length H
length-subHyps n t [] = refl
length-subHyps n t (mkHyp hyp ∷ H) = cong suc (length-subHyps (suc n) t H)


≡subs→length : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H : hypotheses}
             → ≡subs i w s1 s2 H
             → length s1 ≡ length H × length s2 ≡ length H
≡subs→length {i} {w} {.[]} {.[]} {.[]} (≡subs[] .i .w) = refl , refl
≡subs→length {i} {w} {.(t1 ∷ s1)} {.(t2 ∷ s2)} {.(mkHyp T ∷ hs)} (≡subs∷ .i .w t1 t2 s1 s2 T #T hs x h)
  rewrite fst (≡subs→length h) | snd (≡subs→length h) | length-subHyps 0 ⌜ t1 ⌝ hs
  = refl , refl


≡hyps→length : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H1 H2 : hypotheses}
             → ≡hyps i w s1 s2 H1 H2
             → length s1 ≡ length H1 × length s2 ≡ length H2 × length H1 ≡ length H2
≡hyps→length {i} {w} {.[]} {.[]} {.[]} {.[]} (≡hyps[] .i .w) = refl , refl , refl
≡hyps→length {i} {w} {.(t1 ∷ s1)} {.(t2 ∷ s2)} {.(mkHyp T1 ∷ hs1)} {.(mkHyp T2 ∷ hs2)} (≡hyps∷ .i .w t1 t2 s1 s2 T1 #T1 T2 #T2 hs1 hs2 x h)
  rewrite fst (≡hyps→length h) | fst (snd (≡hyps→length h))
  = cong suc (length-subHyps 0 ⌜ t1 ⌝ hs1) ,
    cong suc (length-subHyps 0 ⌜ t2 ⌝ hs2) ,
    cong suc (trans (sym (length-subHyps 0 ⌜ t1 ⌝ hs1)) (trans (snd (snd (≡hyps→length h))) (length-subHyps 0 ⌜ t2 ⌝ hs2)))


-- Lower the variables starting from x+1, removing x
lowerVarsFrom : Var → List Var → List Var
lowerVarsFrom x [] = []
lowerVarsFrom x (0 ∷ l) with x ≟ 0
... | yes p = lowerVarsFrom x l -- ≡ so remove it
... | no  p = 0 ∷ lowerVarsFrom x l -- smaller so keep it
lowerVarsFrom x (suc n ∷ l) with suc n <? x
... | yes p = suc n ∷ lowerVarsFrom x l -- smaller so keep it
... | no  p with x ≟ suc n
... | yes q = lowerVarsFrom x l -- ≡ so remove it
... | no  q = n ∷ lowerVarsFrom x l -- great so lower it


lowerVarsFrom++ : (v : Var) (l k : List Var)
                → lowerVarsFrom v (l ++ k) ≡ lowerVarsFrom v l ++ lowerVarsFrom v k
lowerVarsFrom++ v [] k = refl
lowerVarsFrom++ v (0 ∷ l) k with v ≟ 0
... | yes p rewrite p = lowerVarsFrom++ 0 l k
... | no  p = cong (λ z → 0 ∷ z) (lowerVarsFrom++ v l k)
lowerVarsFrom++ v (suc x ∷ l) k with suc x <? v
... | yes p = cong (λ z → suc x ∷ z) (lowerVarsFrom++ v l k)
... | no  p with v ≟ suc x
... | yes q = lowerVarsFrom++ v l k
... | no  q = cong (λ z → x ∷ z) (lowerVarsFrom++ v l k)


lowerVarsFrom++₃ : (v : Var) (i j k : List Var)
                → lowerVarsFrom v (i ++ j ++ k)
                ≡ lowerVarsFrom v i ++ lowerVarsFrom v j ++ lowerVarsFrom v k
lowerVarsFrom++₃ v i j k
  rewrite lowerVarsFrom++ v i (j ++ k)
        | lowerVarsFrom++ v j k = refl


lowerVarsFrom++₄ : (v : Var) (i j k l : List Var)
                → lowerVarsFrom v (i ++ j ++ k ++ l)
                ≡ lowerVarsFrom v i ++ lowerVarsFrom v j ++ lowerVarsFrom v k ++ lowerVarsFrom v l
lowerVarsFrom++₄ v i j k l
  rewrite lowerVarsFrom++ v i (j ++ k ++ l)
        | lowerVarsFrom++ v j (k ++ l)
        | lowerVarsFrom++ v k l = refl


⊆lowerVarsFrom++ : (v : Var) (l k : List Var)
                 → lowerVarsFrom v l ++ lowerVarsFrom v k ⊆ lowerVarsFrom v (l ++ k)
⊆lowerVarsFrom++ v l k {x} i rewrite lowerVarsFrom++ v l k = i


→predIf≤∈lowerVarsFrom : (k n : ℕ) (l : List Var)
                       → k ∈ removeV n l
                       → predIf≤ n k ∈ lowerVarsFrom n l
→predIf≤∈lowerVarsFrom k n (0 ∷ l) i with 0 ≟ n
... | yes p rewrite sym p = →predIf≤∈lowerVarsFrom k 0 l i
→predIf≤∈lowerVarsFrom k 0 (0 ∷ l) (here px) | no p rewrite px = ⊥-elim (p refl)
→predIf≤∈lowerVarsFrom k (suc n) (0 ∷ l) (here px) | no p rewrite px = here refl
→predIf≤∈lowerVarsFrom k 0 (0 ∷ l) (there i) | no p = ⊥-elim (p refl)
→predIf≤∈lowerVarsFrom k (suc n) (0 ∷ l) (there i) | no p = there (→predIf≤∈lowerVarsFrom k (suc n) l i)
→predIf≤∈lowerVarsFrom k n (suc x ∷ l) i with suc x ≟ n
... | yes p rewrite sym p with suc x <? suc x
... |   yes q = ⊥-elim (<-irrefl refl q)
... |   no q with suc x ≟ suc x
... |     yes r = →predIf≤∈lowerVarsFrom k (suc x) l i
... |     no r = ⊥-elim (r refl)
→predIf≤∈lowerVarsFrom k n (suc x ∷ l) (here px) | no p rewrite px with suc x <? n
... | yes q with x <? n
... |   yes r = here refl
... |   no r = ⊥-elim (r (≤-trans (<⇒≤ ≤-refl) q))
→predIf≤∈lowerVarsFrom k n (suc x ∷ l) (here px) | no p | no q with n ≟ suc x
... | yes r rewrite r = ⊥-elim (p refl)
... | no r with x <? n
... |   yes z = ⊥-elim (q (≤⇒< (suc x) n z p))
... |   no z = here refl
→predIf≤∈lowerVarsFrom k n (suc x ∷ l) (there i) | no p with suc x <? n
... | yes q = there (→predIf≤∈lowerVarsFrom k n l i)
... | no q with n ≟ suc x
... |   yes r rewrite r = →predIf≤∈lowerVarsFrom k (suc x) l i
... |   no r = there (→predIf≤∈lowerVarsFrom k n l i)


fvars-subn⊆ : (n : ℕ) (u t : Term) → fvars (subn n u t) ⊆ lowerVarsFrom n (fvars t) ++ fvars u
fvars-subn⊆ n u t {x} i
  rewrite sym (subn≡sub n u t)
        | fvars-shiftDown≡ n (subv n (shiftUp n u) t)
  with ∈-map⁻ (predIf≤ n) i
... | k , k1 , k2
  rewrite k2
  with ∈-++⁻ (removeV n (fvars t)) (fvars-subv n (shiftUp n u) t {k} k1)
... | inj₁ p = ∈-++⁺ˡ (→predIf≤∈lowerVarsFrom k n (fvars t) p)
... | inj₂ p
  rewrite fvars-shiftUp≡ n u
  with ∈-map⁻ (sucIf≤ n) p
... | j , j1 , j2 rewrite j2 with j <? n
... | yes q rewrite ≤→predIf≤ {j} {n} (≤-trans (<⇒≤ ≤-refl) q) = ∈-++⁺ʳ (lowerVarsFrom n (fvars t)) j1
... | no q with suc j ≤? n
... | yes r = ⊥-elim (q r)
... | no r = ∈-++⁺ʳ (lowerVarsFrom n (fvars t)) j1


∈lowerVarsFrom→ : (x n : Var) (l : List Var)
                → x ∈ lowerVarsFrom n l
                → (x < n × x ∈ l)
                ⊎ (n ≤ x × suc x ∈ l)
∈lowerVarsFrom→ x n (0 ∷ l) i with n ≟ 0
... | yes p rewrite p with ∈lowerVarsFrom→ x 0 l i
... |   inj₁ (q1 , q2) = ⊥-elim (<-irrefl refl (≤-trans q1 _≤_.z≤n))
... |   inj₂ (q1 , q2) = inj₂ (q1 , there q2)
∈lowerVarsFrom→ x n (0 ∷ l) (here px) | no p rewrite px =
  inj₁ (≤⇒< 0 n _≤_.z≤n (λ z → p (sym z)) , here refl)
∈lowerVarsFrom→ x n (0 ∷ l) (there i) | no p with ∈lowerVarsFrom→ x n l i
... |   inj₁ (q1 , q2) = inj₁ (q1 , there q2)
... |   inj₂ (q1 , q2) = inj₂ (q1 , there q2)
∈lowerVarsFrom→ x n (suc y ∷ l) i with suc y <? n
∈lowerVarsFrom→ x n (suc y ∷ l) (here px) | yes p rewrite px = inj₁ (p , here refl)
∈lowerVarsFrom→ x n (suc y ∷ l) (there i) | yes p with ∈lowerVarsFrom→ x n l i
... |   inj₁ (q1 , q2) = inj₁ (q1 , there q2)
... |   inj₂ (q1 , q2) = inj₂ (q1 , there q2)
∈lowerVarsFrom→ x n (suc y ∷ l) i | no p with n ≟ suc y
∈lowerVarsFrom→ x n (suc y ∷ l) i | no p | yes q rewrite q with ∈lowerVarsFrom→ x (suc y) l i
... |   inj₁ (q1 , q2) = inj₁ (q1 , there q2)
... |   inj₂ (q1 , q2) = inj₂ (q1 , there q2)
∈lowerVarsFrom→ x n (suc y ∷ l) (here px) | no p | no q rewrite px =
  inj₂ (s≤s-inj (≤⇒< n (suc y) (≮⇒≥ p) q) , here refl)
∈lowerVarsFrom→ x n (suc y ∷ l) (there i) | no p | no q with ∈lowerVarsFrom→ x n l i
... |   inj₁ (q1 , q2) = inj₁ (q1 , there q2)
... |   inj₂ (q1 , q2) = inj₂ (q1 , there q2)


→∈sdom : (x : Var) (s : Sub)
       → x < length s
       → x ∈ sdom s
→∈sdom 0 (x₁ ∷ s) i = here refl
→∈sdom (suc x) (x₁ ∷ s) i = there (∈-map⁺ suc (→∈sdom x s (s≤s-inj i)))


≡subs→coveredₗ : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H : hypotheses} {A : Term}
              → ≡subs i w s1 s2 H
              → coveredH H A
              → covered s1 A
≡subs→coveredₗ {i} {w} {s1} {s2} {H} {A} eqs cov {x} j =
  →∈sdom x s1 q
  where
  h : x < length H
  h = ∈hdom→ (cov j)

  q : x < length s1
  q rewrite fst (≡subs→length eqs) = h


≡subs→coveredᵣ : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H : hypotheses} {A : Term}
              → ≡subs i w s1 s2 H
              → coveredH H A
              → covered s2 A
≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {A} eqs cov {x} j =
  →∈sdom x s2 q
  where
  h : x < length H
  h = ∈hdom→ (cov j)

  q : x < length s2
  q rewrite snd (≡subs→length eqs) = h


covered∷→ : (t : CTerm) (s : Sub) (F : Term)
          → covered (t ∷ s) F
          → covered s (subn (length s) ⌜ t ⌝ F)
covered∷→ t s F c {x} i with  ∈-++⁻ (lowerVarsFrom (length s) (fvars F)) (fvars-subn⊆ (length s) ⌜ t ⌝ F {x} i)
... | inj₁ p with ∈lowerVarsFrom→ x (length s) (fvars F) p
covered∷→ t s F c {x} i | inj₁ p | inj₁ (q1 , q2) with c {x} q2
... | here px rewrite px = →∈sdom 0 s q1
... | there j with ∈-map⁻ suc j
... |   k , k1 , k2 rewrite k2 = →∈sdom (suc k) s q1
covered∷→ t s F c {x} i | inj₁ p | inj₂ (q1 , q2) with c {suc x} q2
... | here px = ⊥-elim (1+n≢0 px)
... | there j with ∈-map⁻ suc j
... |   k , k1 , k2 rewrite suc-injective k2 = k1
covered∷→ t s F c {x} i | inj₂ p rewrite CTerm.closed t = ⊥-elim (¬∈[] p)


#subs→ : (s : Sub) (t : Term) (#t : # t)
       → subs s t ≡ t
#subs→ [] t #t = refl
#subs→ (x ∷ s) t #t = trans (cong (subn 0 ⌜ x ⌝) (#subs→ s t #t)) (#subn 0 ⌜ x ⌝ t #t)


subn-subs' : (n : ℕ) (t : Term) (s : Sub) (F : Term)
           → subn n (subs s t) (subs s F) ≡ subs s (subn (n + length s) t F)
subn-subs' n t [] F rewrite +0 n = refl
subn-subs' n t (x ∷ s) F =
  trans (sym (subn-subn2 n 0 _≤_.z≤n ⌜ x ⌝ (subs s t) (subs s F) (CTerm.closed x)))
        (cong (subn 0 ⌜ x ⌝) (trans (subn-subs' (suc n) t s F) h))
 where
 h : subs s (subn (suc (n + length s)) t F) ≡ subs s (subn (n + suc (length s)) t F)
 h rewrite sym (+-assoc n 1 (length s)) | +-comm n 1 = refl


subn-subs : (n : ℕ) (t : Term) (#t : # t) (s : Sub) (F : Term)
          → subn n t (subs s F) ≡ subs s (subn (n + length s) t F)
subn-subs n t #t s F =
  trans (cong (λ z → subn n z (subs s F)) (sym (#subs→ s t #t))) (subn-subs' n t s F)


¬0≡s : (n : ℕ) → ¬ 0 ≡ suc n
¬0≡s n ()


¬n≡sn : (n : ℕ) → ¬ n ≡ suc n
¬n≡sn n ()


≤0→≡0 : (n : ℕ) → n ≤ 0 → n ≡ 0
≤0→≡0 0 x = refl
≤0→≡0 (suc n) ()


subn-subn3 : (n m : ℕ) (ltn : n ≤ m) (a b t : Term) (#a : # a)
           → subn m a (subn n b t) ≡ subn n (subn m a b) (subn (suc m) a t)
-- VAR case
subn-subn3 n m ltn a b (VAR x) #a with x ≟ n
subn-subn3 n m ltn a b (VAR x) #a | yes p rewrite p with n ≟ suc m
subn-subn3 n m ltn a b (VAR x) #a | yes p | yes q rewrite q = ⊥-elim (<-irrefl refl ltn)
subn-subn3 0 m ltn a b (VAR x) #a | yes p | no q = refl
subn-subn3 (suc n) m ltn a b (VAR x) #a | yes p | no q with n <? suc m
subn-subn3 (suc n) m ltn a b (VAR x) #a | yes p | no q | yes r with suc n ≟ suc n
... | yes s = refl
... | no s = ⊥-elim (s refl)
subn-subn3 (suc n) m ltn a b (VAR x) #a | yes p | no q | no r = ⊥-elim (r (≤-trans ltn (≤-step ≤-refl)))
subn-subn3 n m ltn a b (VAR x) #a | no p with x ≟ suc m
subn-subn3 n m ltn a b (VAR 0) #a | no p | yes q with 0 ≟ m
subn-subn3 n m ltn a b (VAR 0) #a | no p | yes q | yes r rewrite sym r = ⊥-elim (¬0≡s 0 q)
subn-subn3 n m ltn a b (VAR 0) #a | no p | yes q | no r = ⊥-elim (¬0≡s m q)
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | yes q rewrite suc-injective q with m <? n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | yes q | yes r = ⊥-elim (<-irrefl refl (≤-trans r ltn))
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | yes q | no r with m ≟ m
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | yes q | no r | yes s = sym (#subn n (subn m a b) a #a)
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | yes q | no r | no s = ⊥-elim (s refl)
subn-subn3 n m ltn a b (VAR 0) #a | no p | no q with 0 ≟ n
subn-subn3 n m ltn a b (VAR 0) #a | no p | no q | yes r rewrite sym r = ⊥-elim (p refl)
subn-subn3 n m ltn a b (VAR 0) #a | no p | no q | no r with 0 ≟ m
subn-subn3 n m ltn a b (VAR 0) #a | no p | no q | no r | yes s rewrite sym s = ⊥-elim (r (sym (≤0→≡0 n ltn)))
subn-subn3 n m ltn a b (VAR 0) #a | no p | no q | no r | no s = refl
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q with x <? suc m
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r with x <? n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s with suc x ≟ m
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s | yes i
  rewrite i = ⊥-elim (p (≤∧≮⇒≡ {m} {n} s (≤⇒≯ ltn)))
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s | no i with suc x ≟ n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s | no i | yes j = ⊥-elim (p j)
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s | no i | no j with x <? n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s | no i | no j | yes k with x <? m
... | yes l = refl
... | no l = ⊥-elim (l (≤-trans k ltn))
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | yes s | no i | no j | no k with x <? m
... | yes l = ⊥-elim (k s)
... | no l = refl
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s with suc x ≟ m
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | yes i rewrite i with m ≟ n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | yes i | yes j = ⊥-elim (p j)
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | yes i | no j with x ≟ m
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | yes i | no j | yes l
  rewrite l = ⊥-elim (¬n≡sn m (sym i))
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | yes i | no j | no l
  rewrite sym i | ≤→predIf≤ {x} {suc x} (≤-step ≤-refl) | <→predIf≤2 {n} {suc x} (≰⇒> s) = refl
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | no i with suc x ≟ n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | no i | yes j rewrite j = ⊥-elim (p refl)
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | no i | no j with x <? n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | no i | no j | yes k = ⊥-elim (s k)
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | yes r | no s | no i | no j | no k with x ≟ m
... | yes l rewrite l = ⊥-elim (q refl)
... | no l rewrite ≤→predIf≤ {x} {m} (s≤s-inj r) = refl
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | no r with x <? n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | no r | yes s = ⊥-elim (r (≤-trans s (≤-trans ltn (≤-step ≤-refl))))
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | no r | no s with x ≟ n
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | no r | no s | yes i rewrite i = ⊥-elim (r (_≤_.s≤s ltn))
subn-subn3 n m ltn a b (VAR (suc x)) #a | no p | no q | no r | no s | no i with x ≟ m
... | yes j rewrite j = ⊥-elim (r ≤-refl)
... | no j rewrite <→predIf≤2 {m} {x} (s≤s-inj (≰⇒> r)) | <→predIf≤2 {n} {x} (≤⇒< n x (≮⇒≥ s) (λ z → i (sym z))) = refl
--
subn-subn3 n m ltn a b QNAT #a = refl
subn-subn3 n m ltn a b (LT t t₁) #a =
  cong₂ LT (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (QLT t t₁) #a =
  cong₂ QLT (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (NUM x) #a = refl
subn-subn3 n m ltn a b (IFLT t t₁ t₂ t₃) #a =
  cong₄ IFLT (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a) (subn-subn3 n m ltn a b t₂ #a) (subn-subn3 n m ltn a b t₃ #a)
subn-subn3 n m ltn a b (IFEQ t t₁ t₂ t₃) #a =
 cong₄ IFEQ (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a) (subn-subn3 n m ltn a b t₂ #a) (subn-subn3 n m ltn a b t₃ #a)
subn-subn3 n m ltn a b (SUC t) #a = cong SUC (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (NATREC t t₁ t₂) #a =
  cong₃ NATREC (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a) (subn-subn3 n m ltn a b t₂ #a)
subn-subn3 n m ltn a b (PI t t₁) #a =
  cong₂ PI (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
      (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
         (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (LAMBDA t) #a =
  cong LAMBDA
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t (→#shiftUp 0 {a} #a))
      (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t))
         (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (APPLY t t₁) #a =
  cong₂ APPLY (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (FIX t) #a = cong FIX (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (LET t t₁) #a =
  cong₂ LET (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
      (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
         (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (WT t t₁ t₂) #a =
  cong₃ WT (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
           (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
             (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
    (subn-subn3 n m ltn a b t₂ #a)
subn-subn3 n m ltn a b (SUP t t₁) #a =
  cong₂ SUP (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (WREC t t₁) #a =
  cong₂ WREC (subn-subn3 n m ltn a b t #a)
    (trans
       (subn-subn3 (suc (suc (suc n))) (suc (suc (suc m))) (_≤_.s≤s (_≤_.s≤s (_≤_.s≤s ltn))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b))) t₁ (→#shiftUp 0 {shiftUp 0 (shiftUp 0 a)} (→#shiftUp 0 {shiftUp 0 a} (→#shiftUp 0 {a} #a))))
       (cong
          (λ z → subn (suc (suc (suc n))) z (subn (suc (suc (suc (suc m)))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) t₁))
          (sym (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUp-subn 0 m a b _≤_.z≤n))
                                               (shiftUp-subn 0 (suc m) (shiftUp 0 a) (shiftUp 0 b) _≤_.z≤n)))
                      (shiftUp-subn 0 (suc (suc m)) (shiftUp 0 (shiftUp 0 a)) (shiftUp 0 (shiftUp 0 b)) _≤_.z≤n)))))
subn-subn3 n m ltn a b (MT t t₁ t₂) #a =
  cong₃ MT (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
           (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
             (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
    (subn-subn3 n m ltn a b t₂ #a)
subn-subn3 n m ltn a b (SUM t t₁) #a =
  cong₂ SUM (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
      (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
         (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (PAIR t t₁) #a =
  cong₂ PAIR (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (SPREAD t t₁) #a =
  cong₂ SPREAD (subn-subn3 n m ltn a b t #a)
    (trans
       (subn-subn3 (suc (suc n)) (suc (suc m)) (_≤_.s≤s (_≤_.s≤s ltn)) (shiftUp 0 (shiftUp 0 a)) (shiftUp 0 (shiftUp 0 b)) t₁ (→#shiftUp 0 {shiftUp 0 a} (→#shiftUp 0 {a} #a)))
       (cong
          (λ z → subn (suc (suc n)) z (subn (suc (suc (suc m))) (shiftUp 0 (shiftUp 0 a)) t₁))
          (sym (trans (cong (shiftUp 0) (shiftUp-subn 0 m a b _≤_.z≤n))
                            (shiftUp-subn 0 (suc m) (shiftUp 0 a) (shiftUp 0 b) _≤_.z≤n)))))
subn-subn3 n m ltn a b (SET t t₁) #a =
  cong₂ SET (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
      (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
         (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (TUNION t t₁) #a =
  cong₂ TUNION (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
      (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
         (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (ISECT t t₁) #a =
  cong₂ ISECT (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (UNION t t₁) #a =
  cong₂ UNION (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (INL t) #a = cong INL (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (INR t) #a = cong INR (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (DECIDE t t₁ t₂) #a =
  cong₃ DECIDE (subn-subn3 n m ltn a b t #a)
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₁ (→#shiftUp 0 {a} #a))
           (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₁))
             (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
    (trans (subn-subn3 (suc n) (suc m) (_≤_.s≤s ltn) (shiftUp 0 a) (shiftUp 0 b) t₂ (→#shiftUp 0 {a} #a))
           (cong (λ z → subn (suc n) z (subn (suc (suc m)) (shiftUp 0 a) t₂))
             (sym (shiftUp-subn 0 m a b _≤_.z≤n))))
subn-subn3 n m ltn a b (EQ t t₁ t₂) #a =
  cong₃ EQ (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a) (subn-subn3 n m ltn a b t₂ #a)
subn-subn3 n m ltn a b AX #a = refl
subn-subn3 n m ltn a b FREE #a = refl
subn-subn3 n m ltn a b (CS x) #a = refl
subn-subn3 n m ltn a b (NAME x) #a = refl
subn-subn3 n m ltn a b (FRESH t) #a =
  cong FRESH (trans (subn-subn3 n m ltn (shiftNameUp 0 a) (shiftNameUp 0 b) t (→#shiftNameUp 0 {a} #a))
    (cong (λ z → subn n z (subn (suc m) (shiftNameUp 0 a) t)) (subn-shiftNameUp 0 m a b)))
subn-subn3 n m ltn a b (CHOOSE t t₁) #a =
  cong₂ CHOOSE (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b (LOAD t) #a = refl
subn-subn3 n m ltn a b (MSEQ x) #a = refl
subn-subn3 n m ltn a b (MAPP x t) #a = cong (MAPP x) (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b NOWRITE #a = refl
subn-subn3 n m ltn a b NOREAD #a = refl
subn-subn3 n m ltn a b (SUBSING t) #a = cong SUBSING (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (DUM t) #a = cong DUM (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (FFDEFS t t₁) #a =
  cong₂ FFDEFS (subn-subn3 n m ltn a b t #a) (subn-subn3 n m ltn a b t₁ #a)
subn-subn3 n m ltn a b PURE #a = refl
subn-subn3 n m ltn a b NOSEQ #a = refl
subn-subn3 n m ltn a b NOENC #a = refl
subn-subn3 n m ltn a b (TERM t) #a = cong TERM (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (ENC t) #a = refl
subn-subn3 n m ltn a b (UNIV x) #a = refl
subn-subn3 n m ltn a b (LIFT t) #a = cong LIFT (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (LOWER t) #a = cong LOWER (subn-subn3 n m ltn a b t #a)
subn-subn3 n m ltn a b (SHRINK t) #a = cong SHRINK (subn-subn3 n m ltn a b t #a)


subn-subsN : (n : ℕ) (t : Term) (s : Sub) (F : Term)
           → subn n (subsN n s t) (subsN (suc n) s F) ≡ subsN n s (subn n t F)
subn-subsN n t [] F = refl
subn-subsN n t (x ∷ s) F =
  trans (e1 (subsN (suc n) s F) (subsN n s t)) (cong (subn n ⌜ x ⌝) (subn-subsN n t s F))
  where
  e1 : (u v : Term)
     → subn n (subn n ⌜ x ⌝ v) (subn (suc n) ⌜ x ⌝ u)
     ≡ subn n ⌜ x ⌝ (subn n v u)
  e1 u v = sym (subn-subn3 n n ≤-refl ⌜ x ⌝ v u (CTerm.closed x))


≡subs∷ʳ : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H : hypotheses) (F : Term) (c : covered s1 F) (a₁ a₂ : CTerm)
        → equalInType i w (#subs s1 F c) a₁ a₂
        → ≡subs i w s1 s2 H
        → ≡subs i w (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) (H ∷ʳ mkHyp F)
≡subs∷ʳ i w .[] .[] .[] F c a₁ a₂ a∈ (≡subs[] .i .w) =
  ≡subs∷ i w a₁ a₂ [] [] F (covered[]→# {F} c) [] (≡CTerm→equalInType (CTerm≡ refl) a∈) (≡subs[] i w)
≡subs∷ʳ i w .(t1 ∷ s1) .(t2 ∷ s2) .(mkHyp T ∷ hs) F c a₁ a₂ a∈ (≡subs∷ .i .w t1 t2 s1 s2 T #T hs x h) =
  ≡subs∷ i w t1 t2 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) T #T (hs ∷ʳ mkHyp F) x q1
  where
  c0 : covered s1 (subn (length s1) ⌜ t1 ⌝ F)
  c0 = covered∷→ t1 s1 F c

  c1 : covered s1 (subn (length hs) ⌜ t1 ⌝ F)
  c1 rewrite sym (trans (fst (≡subs→length h)) (length-subHyps 0 ⌜ t1 ⌝ hs)) = c0

  e0 : subs (t1 ∷ s1) F ≡ subs s1 (subn (length hs) ⌜ t1 ⌝ F)
  e0 rewrite sym (trans (fst (≡subs→length h)) (length-subHyps 0 ⌜ t1 ⌝ hs)) =
    subn-subs 0 ⌜ t1 ⌝ (CTerm.closed t1) s1 F

  a∈1 : equalInType i w (#subs s1 (subn (length hs) ⌜ t1 ⌝ F) c1) a₁ a₂
  a∈1 = ≡CTerm→equalInType (CTerm≡ e0) a∈

  q2 : ≡subs i w (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) (subHyps 0 ⌜ t1 ⌝ hs ∷ʳ mkHyp (subn (length hs) ⌜ t1 ⌝ F))
  q2 = ≡subs∷ʳ i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs) (subn (length hs) ⌜ t1 ⌝ F) c1 a₁ a₂ a∈1 h

  q1 : ≡subs i w (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) (subHyps 0 ⌜ t1 ⌝ (hs ∷ʳ mkHyp F))
  q1 rewrite subHyps∷ʳ 0 ⌜ t1 ⌝ F hs = q2


≡hyps∷ʳ : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H1 H2 : hypotheses) (F1 F2 : Term)
          (c1 : covered s1 F1) (c2 : covered s2 F2) (a₁ a₂ : CTerm)
--        → equalInType i w (#subs s1 F c) a₁ a₂
        → equalTypes i w (#subs s1 F1 c1) (#subs s2 F2 c2)
        → ≡hyps i w s1 s2 H1 H2
        → ≡hyps i w (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) (H1 ∷ʳ mkHyp F1) (H2 ∷ʳ mkHyp F2)
≡hyps∷ʳ i w .[] .[] .[] .[] F1 F2 c1 c2 a₁ a₂ a∈ (≡hyps[] .i .w) =
  ≡hyps∷ i w a₁ a₂ [] [] F1 (covered[]→# {F1} c1) F2 (covered[]→# {F2} c2) [] []
    (≡CTerm→eqTypes (CTerm≡ refl) (CTerm≡ refl) a∈)
    (≡hyps[] i w)
≡hyps∷ʳ i w .(t1 ∷ s1) .(t2 ∷ s2) .(mkHyp T1 ∷ hs1) .(mkHyp T2 ∷ hs2) F1 F2 c1 c2 a₁ a₂ a∈ (≡hyps∷ .i .w t1 t2 s1 s2 T1 #T1 T2 #T2 hs1 hs2 x h) =
  ≡hyps∷ i w t1 t2 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) T1 #T1 T2 #T2 (hs1 ∷ʳ mkHyp F1) (hs2 ∷ʳ mkHyp F2) x q1
  where
  e1 : covered s1 (subn (length s1) ⌜ t1 ⌝ F1)
  e1 = covered∷→ t1 s1 F1 c1

  e2 : covered s2 (subn (length s2) ⌜ t2 ⌝ F2)
  e2 = covered∷→ t2 s2 F2 c2

  d1 : covered s1 (subn (length hs1) ⌜ t1 ⌝ F1)
  d1 rewrite sym (trans (fst (≡hyps→length h)) (length-subHyps 0 ⌜ t1 ⌝ hs1)) = e1

  d2 : covered s2 (subn (length hs2) ⌜ t2 ⌝ F2)
  d2 rewrite sym (trans (fst (snd (≡hyps→length h))) (length-subHyps 0 ⌜ t2 ⌝ hs2)) = e2

  x1 : subs (t1 ∷ s1) F1 ≡ subs s1 (subn (length hs1) ⌜ t1 ⌝ F1)
  x1 rewrite sym (trans (fst (≡hyps→length h)) (length-subHyps 0 ⌜ t1 ⌝ hs1)) =
    subn-subs 0 ⌜ t1 ⌝ (CTerm.closed t1) s1 F1

  x2 : subs (t2 ∷ s2) F2 ≡ subs s2 (subn (length hs2) ⌜ t2 ⌝ F2)
  x2 rewrite sym (trans (fst (snd (≡hyps→length h))) (length-subHyps 0 ⌜ t2 ⌝ hs2)) =
    subn-subs 0 ⌜ t2 ⌝ (CTerm.closed t2) s2 F2

  a∈1 : equalTypes i w (#subs s1 (subn (length hs1) ⌜ t1 ⌝ F1) d1) (#subs s2 (subn (length hs2) ⌜ t2 ⌝ F2) d2)
  a∈1 = ≡CTerm→eqTypes (CTerm≡ x1) (CTerm≡ x2) a∈

  q2 : ≡hyps i w (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) (subHyps 0 ⌜ t1 ⌝ hs1 ∷ʳ mkHyp (subn (length hs1) ⌜ t1 ⌝ F1)) (subHyps 0 ⌜ t2 ⌝ hs2 ∷ʳ mkHyp (subn (length hs2) ⌜ t2 ⌝ F2))
  q2 = ≡hyps∷ʳ i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs1) (subHyps 0 ⌜ t2 ⌝ hs2) (subn (length hs1) ⌜ t1 ⌝ F1) (subn (length hs2) ⌜ t2 ⌝ F2) d1 d2 a₁ a₂ a∈1 h

  q1 : ≡hyps i w (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) (subHyps 0 ⌜ t1 ⌝ (hs1 ++ [ mkHyp F1 ])) (subHyps 0 ⌜ t2 ⌝ (hs2 ++ [ mkHyp F2 ]))
  q1 rewrite subHyps∷ʳ 0 ⌜ t1 ⌝ F1 hs1 | subHyps∷ʳ 0 ⌜ t2 ⌝ F2 hs2 = q2


⊆-++ : {L : Level} {A : Set(L)} {a b c d : List A}
     → a ⊆ c
     → b ⊆ d
     → a ++ b ⊆ c ++ d
⊆-++ {L} {A} {a} {b} {c} {d} i j {x} k with ∈-++⁻ a k
... | inj₁ p = ∈-++⁺ˡ (i {x} p)
... | inj₂ p = ∈-++⁺ʳ c (j {x} p)


⊆-++₃ : {L : Level} {A : Set(L)} {a b c d e f : List A}
     → a ⊆ d
     → b ⊆ e
     → c ⊆ f
     → a ++ b ++ c ⊆ d ++ e ++ f
⊆-++₃ {L} {A} {a} {b} {c} {d} {e} {f} i j k {x} p =
  ⊆-++ {L} {A} {a} {b ++ c} {d} {e ++ f} i (⊆-++ {L} {A} {b} {c} {e} {f} j k) p


⊆-++₄ : {L : Level} {A : Set(L)} {a b c d e f g h : List A}
     → a ⊆ e
     → b ⊆ f
     → c ⊆ g
     → d ⊆ h
     → a ++ b ++ c ++ d ⊆ e ++ f ++ g ++ h
⊆-++₄ {L} {A} {a} {b} {c} {d} {e} {f} {g} {h} i j k l {x} p =
  ⊆-++₃ {L} {A} {a} {b} {c ++ d} {e} {f} {g ++ h} i j (⊆-++ {L} {A} k l) p


1≤n : (n : ℕ) → ¬ n ≡ 0 → 1 ≤ n
1≤n 0 p = ⊥-elim (p refl)
1≤n (suc n) p = _≤_.s≤s _≤_.z≤n


lowerVars-lowerVarsFrom : (n : ℕ) (l : List Var) → lowerVars (lowerVarsFrom (suc n) l) ≡ lowerVarsFrom n (lowerVars l)
lowerVars-lowerVarsFrom n [] = refl
lowerVars-lowerVarsFrom n (0 ∷ l) = lowerVars-lowerVarsFrom n l
lowerVars-lowerVarsFrom n (suc 0 ∷ l) with n ≟ 0
lowerVars-lowerVarsFrom n (suc 0 ∷ l) | yes p rewrite p = lowerVars-lowerVarsFrom 0 l
lowerVars-lowerVarsFrom n (suc 0 ∷ l) | no p with 1 <? suc n
... | yes q = cong (λ z → 0 ∷ z) (lowerVars-lowerVarsFrom n l)
... | no q with suc n ≟ 1
... | yes r = ⊥-elim (p (suc-injective r))
... | no r = ⊥-elim (q (_≤_.s≤s (1≤n n p)))
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) with suc x <? n
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) | yes p with suc (suc x) <? suc n
... | yes q = cong (λ z → suc x ∷ z) (lowerVars-lowerVarsFrom n l)
... | no q with suc n ≟ suc (suc x)
... | yes r rewrite suc-injective r = ⊥-elim (<-irrefl refl p)
... | no r = ⊥-elim (q (≤⇒< (suc (suc x)) (suc n) (≤-trans p (<⇒≤ ≤-refl)) (λ z → r (sym z))))
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) | no p with suc (suc x) <? suc n
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) | no p | yes q = ⊥-elim (p (s≤s-inj q))
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) | no p | no q with suc n ≟ suc (suc x)
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) | no p | no q | yes r rewrite suc-injective r with suc x ≟ suc x
... | yes s = lowerVars-lowerVarsFrom (suc x) l
... | no s = ⊥-elim (s refl)
lowerVars-lowerVarsFrom n (suc (suc x) ∷ l) | no p | no q | no r with n ≟ suc x
... | yes s rewrite s = ⊥-elim (r refl)
... | no s = cong (λ z → x ∷ z) (lowerVars-lowerVarsFrom n l)


⊆fvars-subn : (n : ℕ) (u t : Term) → lowerVarsFrom n (fvars t) ⊆ fvars (subn n u t)
⊆fvars-subn n u (VAR 0) {x} i with n ≟ 0
⊆fvars-subn n u (VAR 0) {x} () | yes p
⊆fvars-subn n u (VAR 0) {x} (here i) | no p rewrite i with 0 ≟ n
... | yes r = ⊥-elim (p (sym r))
... | no  r = here refl
⊆fvars-subn n u (VAR (suc v)) {x} i with suc v <? n
⊆fvars-subn n u (VAR (suc v)) {x} (here i) | yes p rewrite i with suc v ≟ n
... | yes r rewrite r = ⊥-elim (<-irrefl refl p)
... | no  r with suc v <? n
⊆fvars-subn n u (VAR (suc v)) {x} (here i) | yes p | no r | yes s with v <? n
... | yes j = here refl
... | no  j = ⊥-elim (j (≤-trans (<⇒≤ ≤-refl) p))
⊆fvars-subn n u (VAR (suc v)) {x} (here i) | yes p | no r | no  s = ⊥-elim (s p)
⊆fvars-subn n u (VAR (suc v)) {x} i | no  p with n ≟ suc v
⊆fvars-subn n u (VAR (suc v)) {x} () | no  p | yes q
⊆fvars-subn n u (VAR (suc v)) {x} (here i) | no  p | no q rewrite i with suc v ≟ n
... | yes r = ⊥-elim (q (sym r))
... | no r with suc v ≤? n
... | yes s = ⊥-elim (p (≤⇒< (suc v) n s r))
... | no s = here refl
⊆fvars-subn n u (LT t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (QLT t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (IFLT t t₁ t₂ t₃) {x} i
  rewrite lowerVarsFrom++₄ n (fvars t) (fvars t₁) (fvars t₂) (fvars t₃)
  = ⊆-++₄ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) (⊆fvars-subn n u t₂) (⊆fvars-subn n u t₃) i
⊆fvars-subn n u (IFEQ t t₁ t₂ t₃) {x} i
  rewrite lowerVarsFrom++₄ n (fvars t) (fvars t₁) (fvars t₂) (fvars t₃)
  = ⊆-++₄ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) (⊆fvars-subn n u t₂) (⊆fvars-subn n u t₃) i
⊆fvars-subn n u (SUC t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (NATREC t t₁ t₂) {x} i
  rewrite lowerVarsFrom++₃ n (fvars t) (fvars t₁) (fvars t₂)
  = ⊆-++₃ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) (⊆fvars-subn n u t₂) i
⊆fvars-subn n u (PI t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (fvars t₁))
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) i
⊆fvars-subn n u (LAMBDA t) {x} i
  rewrite sym (lowerVars-lowerVarsFrom n (fvars t))
  = lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t) i
⊆fvars-subn n u (APPLY t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (FIX t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (LET t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (fvars t₁))
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) i
⊆fvars-subn n u (WT t t₁ t₂) {x} i
  rewrite lowerVarsFrom++₃ n (fvars t) (lowerVars (fvars t₁)) (fvars t₂)
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++₃ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) (⊆fvars-subn n u t₂) i
⊆fvars-subn n u (SUP t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (WREC t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (lowerVars (lowerVars (fvars t₁))))
        | sym (lowerVars-lowerVarsFrom n (lowerVars (lowerVars (fvars t₁))))
        | sym (lowerVars-lowerVarsFrom (suc n) (lowerVars (fvars t₁)))
        | sym (lowerVars-lowerVarsFrom (suc (suc n)) (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (lowerVars⊆lowerVars _ _ (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 u))) t₁)))) i
⊆fvars-subn n u (MT t t₁ t₂) {x} i
  rewrite lowerVarsFrom++₃ n (fvars t) (lowerVars (fvars t₁)) (fvars t₂)
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++₃ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) (⊆fvars-subn n u t₂) i
⊆fvars-subn n u (SUM t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (fvars t₁))
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) i
⊆fvars-subn n u (PAIR t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (SPREAD t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (lowerVars (fvars t₁)))
        | sym (lowerVars-lowerVarsFrom n (lowerVars (fvars t₁)))
        | sym (lowerVars-lowerVarsFrom (suc n) (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc (suc n)) (shiftUp 0 (shiftUp 0 u)) t₁))) i
⊆fvars-subn n u (SET t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (fvars t₁))
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) i
⊆fvars-subn n u (TUNION t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (lowerVars (fvars t₁))
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
  = ⊆-++ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) i
⊆fvars-subn n u (ISECT t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (UNION t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (INL t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (INR t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (DECIDE t t₁ t₂) {x} i
  rewrite lowerVarsFrom++₃ n (fvars t) (lowerVars (fvars t₁)) (lowerVars (fvars t₂))
        | sym (lowerVars-lowerVarsFrom n (fvars t₁))
        | sym (lowerVars-lowerVarsFrom n (fvars t₂))
  = ⊆-++₃ (⊆fvars-subn n u t) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₁)) (lowerVars⊆lowerVars _ _ (⊆fvars-subn (suc n) (shiftUp 0 u) t₂)) i
⊆fvars-subn n u (EQ t t₁ t₂) {x} i
  rewrite lowerVarsFrom++₃ n (fvars t) (fvars t₁) (fvars t₂)
  = ⊆-++₃ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) (⊆fvars-subn n u t₂) i
⊆fvars-subn n u (FRESH t) {x} i = ⊆fvars-subn n (shiftNameUp ℕ.zero u) t i
⊆fvars-subn n u (CHOOSE t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (MAPP x₁ t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (SUBSING t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (DUM t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (FFDEFS t t₁) {x} i
  rewrite lowerVarsFrom++ n (fvars t) (fvars t₁)
  = ⊆-++ (⊆fvars-subn n u t) (⊆fvars-subn n u t₁) i
⊆fvars-subn n u (TERM t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (LIFT t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (LOWER t) {x} i = ⊆fvars-subn n u t i
⊆fvars-subn n u (SHRINK t) {x} i = ⊆fvars-subn n u t i


lowerVarsFrom0 : (l : List Var) → lowerVarsFrom 0 l ≡ lowerVars l
lowerVarsFrom0 [] = refl
lowerVarsFrom0 (0 ∷ l) = lowerVarsFrom0 l
lowerVarsFrom0 (suc x ∷ l) = cong (λ z → x ∷ z) (lowerVarsFrom0 l)


covered-subn→ : (t : CTerm) (u : Term) (s : Sub) (F : Term)
              → covered s (subn 0 u F)
              → covered (s ∷ʳ t) F
covered-subn→ t u s F cov {x} i =
  →covered∷ʳ t s F cov' {x} i
  where
  c : lowerVars (fvars F) ⊆ lowerVarsFrom 0 (fvars F)
  c rewrite lowerVarsFrom0 (fvars F) = λ z → z

  cov' : covered0 s F
  cov' {y} j = cov {y} (⊆fvars-subn 0 u F (c j))

\end{code}
