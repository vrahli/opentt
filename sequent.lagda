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
  using (NATREC⇓ ; predIf≤-sucIf≤ ; subv# ; →#shiftUp ; →#shiftDown ; shiftUp-shiftNameUp ; ¬Names-sub ;
         ¬Seq-sub ; ¬Enc-sub ; ∧≡true→ₗ ; ∧≡true→ᵣ ; #subv)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (shiftNameUp-shiftNameUp)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (lowerVars++⊆ ; lowerVars-fvars-shiftUp ; lowerVars-fvars-shiftUp⊆ ; lowerVars++ ; lowerVars2++⊆ ;
         lowerVars2-fvars-shiftUp⊆ ; sub-shiftUp0≡)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM!)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon ; weq-ext-eq ; meq-ext-eq ; TUNIONeq-ext-eq)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqInType-ext ; □·EqTypes→uniUpTo ; uniUpTo→□·EqTypes ; TEQrefl-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-mon ; ≡CTerm→equalInType ; ≡CTerm→eqTypes ; equalTypes→equalInType-UNIV ; eqTypesUniv ;
         wPredExtIrr-eqInType ; wPredDepExtIrr-eqInType ; wPredDepExtIrr-eqInType2 ; equalInType-refl ; equalInType-sym ;
         equalInType-EQ ; equalInType-NAT!→)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-NAT!)


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


valid≡𝕎 : (n : ℕ) (H : hypotheses) (a b T : Term) → Set(lsuc(L))
valid≡𝕎 n H a b T = (w : 𝕎·) → valid≡ n w H a b T


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


subs-NUM : (s : Sub) (i : ℕ)
         → subs s (NUM i) ≡ NUM i
subs-NUM [] i = refl
subs-NUM (x ∷ s) i rewrite subs-NUM s i = refl


#subs-NUM : (s : Sub) (i : ℕ) (c : covered s (NUM i))
          → #subs s (NUM i) c ≡ #NUM i
#subs-NUM s i c = CTerm≡ (subs-NUM s i)


subsN-NUM : (n : ℕ) (s : Sub) (i : ℕ)
          → subsN n s (NUM i) ≡ NUM i
subsN-NUM n [] i = refl
subsN-NUM n (x ∷ s) i rewrite subsN-NUM n s i = refl


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


subsN-PI : (n : ℕ) (s : Sub) (a b : Term)
         → subsN n s (PI a b) ≡ PI (subsN n s a) (subsN (suc n) s b)
subsN-PI n [] a b = refl
subsN-PI n (x ∷ s) a b
  rewrite subsN-PI n s a b
        | #shiftUp 0 x = refl


coveredPI₁ : {s : Sub} {a b : Term}
           → covered s (PI a b)
           → covered s a
coveredPI₁ {s} {a} {b} c {x} i = c {x} (∈-++⁺ˡ i)


coveredPI₂ : {s : Sub} {a b : Term}
           → covered s (PI a b)
           → covered0 s b
coveredPI₂ {s} {a} {b} c {x} i = c {x} (∈-++⁺ʳ (fvars a) i)


coveredAPPLY₁ : {s : Sub} {a b : Term}
              → covered s (APPLY a b)
              → covered s a
coveredAPPLY₁ {s} {a} {b} c {x} i = c {x} (∈-++⁺ˡ i)


coveredAPPLY₂ : {s : Sub} {a b : Term}
              → covered s (APPLY a b)
              → covered s b
coveredAPPLY₂ {s} {a} {b} c {x} i = c {x} (∈-++⁺ʳ (fvars a) i)


coveredPAIR₁ : {s : Sub} {a b : Term}
             → covered s (PAIR a b)
             → covered s a
coveredPAIR₁ {s} {a} {b} c {x} i = c {x} (∈-++⁺ˡ i)


coveredPAIR₂ : {s : Sub} {a b : Term}
             → covered s (PAIR a b)
             → covered s b
coveredPAIR₂ {s} {a} {b} c {x} i = c {x} (∈-++⁺ʳ (fvars a) i)


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


covered0-UNIV : (s : Sub) (i : ℕ) → covered0 s (UNIV i)
covered0-UNIV s i ()


covered-NUM : (s : Sub) (i : ℕ) → covered s (NUM i)
covered-NUM s i ()


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


coveredEQ₁ : {s : Sub} {a b c : Term}
           → covered s (EQ a b c)
           → covered s a
coveredEQ₁ {s} {a} {b} {c} cov {x} i = cov {x} (∈-++⁺ˡ i)


coveredEQ₂ : {s : Sub} {a b c : Term}
           → covered s (EQ a b c)
           → covered s b
coveredEQ₂ {s} {a} {b} {c} cov {x} i = cov {x} (∈-++⁺ʳ (fvars a) (∈-++⁺ˡ i))


coveredEQ₃ : {s : Sub} {a b c : Term}
           → covered s (EQ a b c)
           → covered s c
coveredEQ₃ {s} {a} {b} {c} cov {x} i = cov {x} (∈-++⁺ʳ (fvars a) (∈-++⁺ʳ (fvars b) i))


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


#subs-EQ : (s : Sub) (a b c : Term) (ce : covered s (EQ a b c)) (ca : covered s a) (cb : covered s b) (cc : covered s c)
         → #subs s (EQ a b c) ce ≡ #EQ (#subs s a ca) (#subs s b cb) (#subs s c cc)
#subs-EQ s a b c ce ca cb cc = CTerm≡ (subs-EQ s a b c)


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


subs-APPLY : (s : Sub) (a b : Term)
           → subs s (APPLY a b) ≡ APPLY (subs s a) (subs s b)
subs-APPLY [] a b = refl
subs-APPLY (x ∷ s) a b
  rewrite subs-APPLY s a b
  = refl


#subs-APPLY : (s : Sub) (a b : Term) (c : covered s (APPLY a b)) (ca : covered s a) (cb : covered s b)
            → #subs s (APPLY a b) c ≡ #APPLY (#subs s a ca) (#subs s b cb)
#subs-APPLY s a b c ca cb = CTerm≡ (subs-APPLY s a b)


subs-PAIR : (s : Sub) (a b : Term)
          → subs s (PAIR a b) ≡ PAIR (subs s a) (subs s b)
subs-PAIR [] a b = refl
subs-PAIR (x ∷ s) a b
  rewrite subs-PAIR s a b
  = refl


#subs-PAIR : (s : Sub) (a b : Term) (c : covered s (PAIR a b)) (ca : covered s a) (cb : covered s b)
           → #subs s (PAIR a b) c ≡ #PAIR (#subs s a ca) (#subs s b cb)
#subs-PAIR s a b c ca cb = CTerm≡ (subs-PAIR s a b)


coveredLAMBDA : {s : Sub} {a : Term}
              → covered s (LAMBDA a)
              → covered0 s a
coveredLAMBDA {s} {a} c = c


subs-LAMBDA : (s : Sub) (a : Term)
            → subs s (LAMBDA a) ≡ LAMBDA (subsN 1 s a)
subs-LAMBDA [] a = refl
subs-LAMBDA (x ∷ s) a
  rewrite subs-LAMBDA s a
        | #shiftUp 0 x = refl


#subs-LAMBDA : (s : Sub) (a : Term) (c : covered s (LAMBDA a)) (ca : covered0 s a)
             → #subs s (LAMBDA a) c ≡ #LAMBDA (#[0]subs s a ca)
#subs-LAMBDA s a c ca = CTerm≡ (subs-LAMBDA s a)


#subs-LAMBDA2 : (s : Sub) (a : Term) (c : covered s (LAMBDA a))
              → #subs s (LAMBDA a) c ≡ #LAMBDA (#[0]subs s a (coveredLAMBDA {s} {a} c))
#subs-LAMBDA2 s a c = #subs-LAMBDA s a c (coveredLAMBDA {s} {a} c)


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
shiftUp-subn n m a (PARTIAL b) len = cong PARTIAL (shiftUp-subn n m a b len)
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


shiftUp-subi : (n m : ℕ) (a b : Term)
             → n ≤ m
             → shiftUp n (subi m a b) ≡ subi (suc m) (shiftUp n a) (shiftUp n b)
-- VAR case
shiftUp-subi n m a (VAR x) len with x ≟ m
shiftUp-subi n m a (VAR x) len | yes p rewrite p with m <? n
shiftUp-subi n m a (VAR x) len | yes p | yes q with m ≟ suc m
... | yes r = refl
... | no r = ⊥-elim (<-irrefl refl (≤-trans q len))
shiftUp-subi n m a (VAR x) len | yes p | no q with suc m ≟ suc m
... | yes r = refl
... | no r = ⊥-elim (r refl)
shiftUp-subi n m a (VAR x) len | no p with x <? n
shiftUp-subi n m a (VAR x) len | no p | yes q with x ≟ suc m
... | yes r rewrite r = ⊥-elim (<-irrefl refl (≤-trans (_≤_.s≤s (≤-trans len (≤-step ≤-refl))) q))
... | no r = refl
shiftUp-subi n m a (VAR x) len | no p | no q with suc x ≟ suc m
... | yes r rewrite suc-injective r = ⊥-elim (p refl)
... | no r = refl
--
shiftUp-subi n m a QNAT len = refl
shiftUp-subi n m a (LT b b₁) len =
  cong₂ LT (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (QLT b b₁) len =
  cong₂ QLT (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (NUM x) len = refl
shiftUp-subi n m a (IFLT b b₁ b₂ b₃) len =
  cong₄ IFLT (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len) (shiftUp-subi n m a b₂ len) (shiftUp-subi n m a b₃ len)
shiftUp-subi n m a (IFEQ b b₁ b₂ b₃) len =
  cong₄ IFEQ (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len) (shiftUp-subi n m a b₂ len) (shiftUp-subi n m a b₃ len)
shiftUp-subi n m a (SUC b) len = cong SUC (shiftUp-subi n m a b len)
shiftUp-subi n m a (NATREC b b₁ b₂) len =
  cong₃ NATREC (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len) (shiftUp-subi n m a b₂ len)
shiftUp-subi n m a (PI b b₁) len =
  cong₂ PI (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (LAMBDA b) len =
  cong LAMBDA
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (APPLY b b₁) len =
  cong₂ APPLY (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (FIX b) len = cong FIX (shiftUp-subi n m a b len)
shiftUp-subi n m a (LET b b₁) len =
  cong₂ LET (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (WT b b₁ b₂) len =
  cong₃ WT (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
        (shiftUp-subi n m a b₂ len)
shiftUp-subi n m a (SUP b b₁) len =
  cong₂ SUP (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (WREC b b₁) len =
  cong₂ WREC (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc (suc (suc n))) (suc (suc (suc m))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) b₁ (_≤_.s≤s (_≤_.s≤s (_≤_.s≤s len))))
               (cong (λ z → subi (suc (suc (suc (suc m)))) z (shiftUp (suc (suc (suc n))) b₁))
                     (sym (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUpUp 0 n a _≤_.z≤n))
                                                          (shiftUpUp 0 (suc n) (shiftUp 0 a) _≤_.z≤n)))
                                 (shiftUpUp 0 (suc (suc n)) (shiftUp 0 (shiftUp 0 a)) _≤_.z≤n)))))
shiftUp-subi n m a (MT b b₁ b₂) len =
  cong₃ MT (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
        (shiftUp-subi n m a b₂ len)
shiftUp-subi n m a (SUM b b₁) len =
  cong₂ SUM (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (PAIR b b₁) len =
  cong₂ PAIR (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (SPREAD b b₁) len =
  cong₂ SPREAD (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc (suc n)) (suc (suc m)) (shiftUp 0 (shiftUp 0 a)) b₁ (_≤_.s≤s (_≤_.s≤s len)))
               (cong (λ z → subi (suc (suc (suc m))) z (shiftUp (suc (suc n)) b₁))
                     (sym (trans (cong (shiftUp 0) (shiftUpUp 0 n a _≤_.z≤n))
                                 (shiftUpUp 0 (suc n) (shiftUp 0 a) _≤_.z≤n)))))
shiftUp-subi n m a (SET b b₁) len =
  cong₂ SET (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (TUNION b b₁) len =
  cong₂ TUNION (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (ISECT b b₁) len =
  cong₂ ISECT (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (UNION b b₁) len =
  cong₂ UNION (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (INL b) len = cong INL (shiftUp-subi n m a b len)
shiftUp-subi n m a (INR b) len = cong INR (shiftUp-subi n m a b len)
shiftUp-subi n m a (DECIDE b b₁ b₂) len =
  cong₃ DECIDE (shiftUp-subi n m a b len)
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₁ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₁)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
        (trans (shiftUp-subi (suc n) (suc m) (shiftUp 0 a) b₂ (_≤_.s≤s len))
               (cong (λ z → subi (suc (suc m)) z (shiftUp (suc n) b₂)) (sym (shiftUpUp 0 n a _≤_.z≤n))))
shiftUp-subi n m a (EQ b b₁ b₂) len =
  cong₃ EQ (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len) (shiftUp-subi n m a b₂ len)
shiftUp-subi n m a AX len = refl
shiftUp-subi n m a FREE len = refl
shiftUp-subi n m a (CS x) len = refl
shiftUp-subi n m a (NAME x) len = refl
shiftUp-subi n m a (FRESH b) len =
  cong FRESH (trans (shiftUp-subi n m (shiftNameUp 0 a) b len)
                    (cong (λ z → subi (suc m) z (shiftUp n b)) (shiftUp-shiftNameUp n 0 a)))
shiftUp-subi n m a (CHOOSE b b₁) len =
  cong₂ CHOOSE (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a (LOAD b) len = refl
shiftUp-subi n m a (MSEQ x) len = refl
shiftUp-subi n m a (MAPP x b) len = cong (MAPP x) (shiftUp-subi n m a b len)
shiftUp-subi n m a NOWRITE len = refl
shiftUp-subi n m a NOREAD len = refl
shiftUp-subi n m a (SUBSING b) len = cong SUBSING (shiftUp-subi n m a b len)
shiftUp-subi n m a (PARTIAL b) len = cong PARTIAL (shiftUp-subi n m a b len)
shiftUp-subi n m a (FFDEFS b b₁) len =
  cong₂ FFDEFS (shiftUp-subi n m a b len) (shiftUp-subi n m a b₁ len)
shiftUp-subi n m a PURE len = refl
shiftUp-subi n m a NOSEQ len = refl
shiftUp-subi n m a NOENC len = refl
shiftUp-subi n m a (TERM b) len = cong TERM (shiftUp-subi n m a b len)
shiftUp-subi n m a (ENC b) len = refl
shiftUp-subi n m a (UNIV x) len = refl
shiftUp-subi n m a (LIFT b) len = cong LIFT (shiftUp-subi n m a b len)
shiftUp-subi n m a (LOWER b) len = cong LOWER (shiftUp-subi n m a b len)
shiftUp-subi n m a (SHRINK b) len = cong SHRINK (shiftUp-subi n m a b len)


shiftNameUp-subn : (m n : ℕ) (a b : Term)
                 → shiftNameUp m (subn n a b)
                 ≡ subn n (shiftNameUp m a) (shiftNameUp m b)
shiftNameUp-subn m n a (VAR x) with x ≟ m
shiftNameUp-subn m n a (VAR x) | yes p rewrite p with m ≟ n
... | yes q = refl
... | no q = refl
shiftNameUp-subn m n a (VAR x) | no p with x ≟ n
... | yes q = refl
... | no q = refl
shiftNameUp-subn m n a QNAT = refl
shiftNameUp-subn m n a (LT b b₁) =
  cong₂ LT (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (QLT b b₁) =
  cong₂ QLT (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (NUM x) = refl
shiftNameUp-subn m n a (IFLT b b₁ b₂ b₃) =
  cong₄ IFLT (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁) (shiftNameUp-subn m n a b₂) (shiftNameUp-subn m n a b₃)
shiftNameUp-subn m n a (IFEQ b b₁ b₂ b₃) =
  cong₄ IFEQ (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁) (shiftNameUp-subn m n a b₂) (shiftNameUp-subn m n a b₃)
shiftNameUp-subn m n a (SUC b) = cong SUC (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (NATREC b b₁ b₂) =
  cong₃ NATREC (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁) (shiftNameUp-subn m n a b₂)
shiftNameUp-subn m n a (PI b b₁) =
  cong₂ PI (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (LAMBDA b) =
  cong LAMBDA
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b)
           (cong (λ z → subn (suc n) z (shiftNameUp m b))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (APPLY b b₁) =
  cong₂ APPLY (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (FIX b) = cong FIX (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (LET b b₁) =
  cong₂ LET (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (WT b b₁ b₂) =
  cong₃ WT (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
    (shiftNameUp-subn m n a b₂)
shiftNameUp-subn m n a (SUP b b₁) =
  cong₂ SUP (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (WREC b b₁) =
  cong₂ WREC (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) b₁)
           (cong (λ z → subn (suc (suc (suc n))) z (shiftNameUp m b₁))
                 (sym (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUp-shiftNameUp 0 m a))
                                                      (shiftUp-shiftNameUp 0 m (shiftUp 0 a))))
                             (shiftUp-shiftNameUp 0 m (shiftUp 0 (shiftUp 0 a)))))))
shiftNameUp-subn m n a (MT b b₁ b₂) =
  cong₃ MT (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
    (shiftNameUp-subn m n a b₂)
shiftNameUp-subn m n a (SUM b b₁) =
  cong₂ SUM (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (PAIR b b₁) =
  cong₂ PAIR (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (SPREAD b b₁) =
  cong₂ SPREAD (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc (suc n)) (shiftUp 0 (shiftUp 0 a)) b₁)
           (cong (λ z → subn (suc (suc n)) z (shiftNameUp m b₁))
                 (sym (trans (cong (shiftUp 0) (shiftUp-shiftNameUp 0 m a))
                             (shiftUp-shiftNameUp 0 m (shiftUp 0 a))))))
shiftNameUp-subn m n a (SET b b₁) =
  cong₂ SET (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (TUNION b b₁) =
  cong₂ TUNION (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (ISECT b b₁) =
  cong₂ ISECT (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (UNION b b₁) =
  cong₂ UNION (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (INL b) = cong INL (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (INR b) = cong INR (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (DECIDE b b₁ b₂) =
  cong₃ DECIDE (shiftNameUp-subn m n a b)
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₁)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₁))
                 (sym (shiftUp-shiftNameUp 0 m a))))
    (trans (shiftNameUp-subn m (suc n) (shiftUp 0 a) b₂)
           (cong (λ z → subn (suc n) z (shiftNameUp m b₂))
                 (sym (shiftUp-shiftNameUp 0 m a))))
shiftNameUp-subn m n a (EQ b b₁ b₂) =
  cong₃ EQ (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁) (shiftNameUp-subn m n a b₂)
shiftNameUp-subn m n a AX = refl
shiftNameUp-subn m n a FREE = refl
shiftNameUp-subn m n a (CS x) = refl
shiftNameUp-subn m n a (NAME x) = refl
shiftNameUp-subn m n a (FRESH b) =
  cong FRESH
    (trans (shiftNameUp-subn (suc m) n (shiftNameUp 0 a) b)
           (cong (λ z → subn n z (shiftNameUp (suc m) b))
                 (sym (shiftNameUp-shiftNameUp {0} {m} {a} _≤_.z≤n))))
shiftNameUp-subn m n a (CHOOSE b b₁) =
  cong₂ CHOOSE (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a (LOAD b) = refl
shiftNameUp-subn m n a (MSEQ x) = refl
shiftNameUp-subn m n a (MAPP x b) = cong (MAPP x) (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a NOWRITE = refl
shiftNameUp-subn m n a NOREAD = refl
shiftNameUp-subn m n a (SUBSING b) = cong SUBSING (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (PARTIAL b) = cong PARTIAL (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (FFDEFS b b₁) =
  cong₂ FFDEFS (shiftNameUp-subn m n a b) (shiftNameUp-subn m n a b₁)
shiftNameUp-subn m n a PURE = refl
shiftNameUp-subn m n a NOSEQ = refl
shiftNameUp-subn m n a NOENC = refl
shiftNameUp-subn m n a (TERM b) = cong TERM (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (ENC b) = refl
shiftNameUp-subn m n a (UNIV x) = refl
shiftNameUp-subn m n a (LIFT b) = cong LIFT (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (LOWER b) = cong LOWER (shiftNameUp-subn m n a b)
shiftNameUp-subn m n a (SHRINK b) = cong SHRINK (shiftNameUp-subn m n a b)


subn-subi : (n : ℕ) (a b c : Term)
          → subn n a (subi n b c) ≡ subn n (subn n a b) c
-- VAR
subn-subi n a b (VAR x) with x ≟ n
... | yes p = refl
... | no p with x ≟ n
... | yes q = ⊥-elim (p q)
... | no q = refl
--
subn-subi n a b QNAT = refl
subn-subi n a b (LT c c₁) =
  cong₂ LT (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (QLT c c₁) =
  cong₂ QLT (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (NUM x) = refl
subn-subi n a b (IFLT c c₁ c₂ c₃) =
  cong₄ IFLT (subn-subi n a b c) (subn-subi n a b c₁) (subn-subi n a b c₂) (subn-subi n a b c₃)
subn-subi n a b (IFEQ c c₁ c₂ c₃) =
  cong₄ IFEQ (subn-subi n a b c) (subn-subi n a b c₁) (subn-subi n a b c₂) (subn-subi n a b c₃)
subn-subi n a b (SUC c) = cong SUC (subn-subi n a b c)
subn-subi n a b (NATREC c c₁ c₂) =
  cong₃ NATREC (subn-subi n a b c) (subn-subi n a b c₁) (subn-subi n a b c₂)
subn-subi n a b (PI c c₁) =
  cong₂ PI
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (LAMBDA c) =
  cong LAMBDA
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c)
           (cong (λ z → subn (suc n) z c) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (APPLY c c₁) =
  cong₂ APPLY (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (FIX c) = cong FIX (subn-subi n a b c)
subn-subi n a b (LET c c₁) =
  cong₂ LET
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (WT c c₁ c₂) =
  cong₃ WT
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
    (subn-subi n a b c₂)
subn-subi n a b (SUP c c₁) =
  cong₂ SUP (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (WREC c c₁) =
  cong₂ WREC
    (subn-subi n a b c)
    (trans (subn-subi (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b))) c₁)
           (cong (λ z → subn (suc (suc (suc n))) z c₁)
                 (sym (trans (cong (shiftUp 0) (trans (cong (shiftUp 0) (shiftUp-subn 0 n a b _≤_.z≤n))
                                                      (shiftUp-subn 0 (suc n) (shiftUp 0 a) (shiftUp 0 b) _≤_.z≤n)))
                             (shiftUp-subn 0 (suc (suc n)) (shiftUp 0 (shiftUp 0 a)) (shiftUp 0 (shiftUp 0 b)) _≤_.z≤n)))))
subn-subi n a b (MT c c₁ c₂) =
  cong₃ MT
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
    (subn-subi n a b c₂)
subn-subi n a b (SUM c c₁) =
  cong₂ SUM
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (PAIR c c₁) =
  cong₂ PAIR (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (SPREAD c c₁) =
  cong₂ SPREAD
    (subn-subi n a b c)
    (trans (subn-subi (suc (suc n)) (shiftUp 0 (shiftUp 0 a)) (shiftUp 0 (shiftUp 0 b)) c₁)
           (cong (λ z → subn (suc (suc n)) z c₁)
                 (sym (trans (cong (shiftUp 0) (shiftUp-subn 0 n a b _≤_.z≤n))
                             (shiftUp-subn 0 (suc n) (shiftUp 0 a) (shiftUp 0 b) _≤_.z≤n)))))
subn-subi n a b (SET c c₁) =
  cong₂ SET
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (TUNION c c₁) =
  cong₂ TUNION
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (ISECT c c₁) =
  cong₂ ISECT (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (UNION c c₁) =
  cong₂ UNION (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (INL c) = cong INL (subn-subi n a b c)
subn-subi n a b (INR c) = cong INR (subn-subi n a b c)
subn-subi n a b (DECIDE c c₁ c₂) =
  cong₃ DECIDE
    (subn-subi n a b c)
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₁)
           (cong (λ z → subn (suc n) z c₁) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
    (trans (subn-subi (suc n) (shiftUp 0 a) (shiftUp 0 b) c₂)
           (cong (λ z → subn (suc n) z c₂) (sym (shiftUp-subn 0 n a b _≤_.z≤n))))
subn-subi n a b (EQ c c₁ c₂) =
  cong₃ EQ (subn-subi n a b c) (subn-subi n a b c₁) (subn-subi n a b c₂)
subn-subi n a b AX = refl
subn-subi n a b FREE = refl
subn-subi n a b (CS x) = refl
subn-subi n a b (NAME x) = refl
subn-subi n a b (FRESH c) =
  cong FRESH (trans (subn-subi n (shiftNameUp 0 a) (shiftNameUp 0 b) c)
                    (cong (λ z → subn n z c) (sym (shiftNameUp-subn 0 n a b))))
subn-subi n a b (CHOOSE c c₁) =
  cong₂ CHOOSE (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b (LOAD c) = refl
subn-subi n a b (MSEQ x) = refl
subn-subi n a b (MAPP x c) = cong (MAPP x) (subn-subi n a b c)
subn-subi n a b NOWRITE = refl
subn-subi n a b NOREAD = refl
subn-subi n a b (SUBSING c) = cong SUBSING (subn-subi n a b c)
subn-subi n a b (PARTIAL c) = cong PARTIAL (subn-subi n a b c)
subn-subi n a b (FFDEFS c c₁) =
  cong₂ FFDEFS (subn-subi n a b c) (subn-subi n a b c₁)
subn-subi n a b PURE = refl
subn-subi n a b NOSEQ = refl
subn-subi n a b NOENC = refl
subn-subi n a b (TERM c) = cong TERM (subn-subi n a b c)
subn-subi n a b (ENC c) = refl
subn-subi n a b (UNIV x) = refl
subn-subi n a b (LIFT c) = cong LIFT (subn-subi n a b c)
subn-subi n a b (LOWER c) = cong LOWER (subn-subi n a b c)
subn-subi n a b (SHRINK c) = cong SHRINK (subn-subi n a b c)


subsN-suc-shiftUp : (n : ℕ) (s : Sub) (b : Term)
                  → subsN (suc n) s (shiftUp 0 b) ≡ shiftUp 0 (subsN n s b)
subsN-suc-shiftUp n [] b = refl
subsN-suc-shiftUp n (x ∷ s) b
  rewrite shiftUp-subn 0 n ⌜ x ⌝ (subsN n s b) _≤_.z≤n
        | subsN-suc-shiftUp n s b
        | #shiftUp 0 x
  = refl


subsN-FUN : (n : ℕ) (s : Sub) (a b : Term)
         → subsN n s (FUN a b) ≡ FUN (subsN n s a) (subsN n s b)
subsN-FUN n s a b
  rewrite subsN-PI n s a (shiftUp 0 b)
  = ≡PI refl (subsN-suc-shiftUp n s b)


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
subn-shiftNameUp n m a (PARTIAL b) = cong PARTIAL (subn-shiftNameUp n m a b)
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
subn-subn2 n m ltn a b (PARTIAL t) ca = cong PARTIAL (subn-subn2 n m ltn a b t ca)
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
subn-subn3 n m ltn a b (PARTIAL t) #a = cong PARTIAL (subn-subn3 n m ltn a b t #a)
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
⊆fvars-subn n u (PARTIAL t) {x} i = ⊆fvars-subn n u t i
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


covered-subn→covered0 : (u : Term) (s : Sub) (F : Term)
                      → covered s (subn 0 u F)
                      → covered0 s F
covered-subn→covered0 u s F cov =
  cov'
  where
  c : lowerVars (fvars F) ⊆ lowerVarsFrom 0 (fvars F)
  c rewrite lowerVarsFrom0 (fvars F) = λ z → z

  cov' : covered0 s F
  cov' {y} j = cov {y} (⊆fvars-subn 0 u F (c j))


covered-subn→ : (t : CTerm) (u : Term) (s : Sub) (F : Term)
              → covered s (subn 0 u F)
              → covered (s ∷ʳ t) F
covered-subn→ t u s F cov =
  →covered∷ʳ t s F (covered-subn→covered0 u s F cov)


→∈raiseVars : {x : Var} {l : List Var}
            → x ∈ l
            → suc x ∈ raiseVars l
→∈raiseVars {x} {l} i = ∈-map⁺ suc i


suc∈sdom∷ʳ : {n : ℕ} {s : Sub} {t : CTerm}
           → suc n ∈ sdom (s ∷ʳ t)
           → n ∈ sdom s
suc∈sdom∷ʳ {n} {[]} {t} (here ())
suc∈sdom∷ʳ {n} {[]} {t} (there ())
suc∈sdom∷ʳ {0} {x ∷ s} {t} (there i) = here refl
suc∈sdom∷ʳ {suc n} {x ∷ s} {t} (there i) =
  there (→∈raiseVars (suc∈sdom∷ʳ {n} {s} {t} (∈raiseVars→ {suc n} {sdom (s ∷ʳ t)} i)))


→covered-subn : (t : CTerm) (u : Term) (s : Sub) (F : Term) (#u : # u)
              → covered (s ∷ʳ t) F
              → covered s (subn 0 u F)
→covered-subn t u s F #u cov {x} i with ∈-++⁻ (lowerVarsFrom 0 (fvars F)) (fvars-subn⊆ 0 u F {x} i)
→covered-subn t u s F #u cov {x} i | inj₁ p with ∈lowerVarsFrom→ x 0 (fvars F) p
... | inj₁ (() , p2)
... | inj₂ (p1 , p2) = suc∈sdom∷ʳ {x} {s} {t} (cov {suc x} p2)
→covered-subn t u s F #u cov {x} i | inj₂ p rewrite #u = ⊥-elim (¬∈[] p)


≡subs-refl : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H : hypotheses)
           → ≡subs i w s1 s2 H
           → ≡subs i w s1 s1 H
≡subs-refl i w .[] .[] .[] (≡subs[] .i .w) = ≡subs[] i w
≡subs-refl i w .(t1 ∷ s1) .(t2 ∷ s2) .(mkHyp T ∷ hs) (≡subs∷ .i .w t1 t2 s1 s2 T #T hs x h) =
  ≡subs∷ i w t1 t1 s1 s1 T #T hs (equalInType-refl x) (≡subs-refl i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs) h)


≡hyps-refl : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H1 H2 : hypotheses)
           → ≡hyps i w s1 s2 H1 H2
           → ≡hyps i w s1 s1 H1 H1
≡hyps-refl u w .[] .[] .[] .[] (≡hyps[] .u .w) = ≡hyps[] u w
≡hyps-refl u w .(t1 ∷ s1) .(t2 ∷ s2) .(mkHyp T1 ∷ hs1) .(mkHyp T2 ∷ hs2) (≡hyps∷ .u .w t1 t2 s1 s2 T1 #T1 T2 #T2 hs1 hs2 x h) =
  ≡hyps∷ u w t1 t1 s1 s1 T1 #T1 T1 #T1 hs1 hs1 (TEQrefl-equalTypes u w (ct T1 #T1) (ct T2 #T2) x)
    (≡hyps-refl u w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs1) (subHyps 0 ⌜ t2 ⌝ hs2) h)



subs∷ʳ≡ : (s : Sub) (k G : Term) (ck : covered s k)
        → subs (s ∷ʳ #subs s k ck) G
        ≡ subs s (subn 0 k G)
subs∷ʳ≡ s k G ck =
  trans (sym (subn-subsN1 (#subs s k ck) s G)) e
  where
  e : subn 0 (subs s k) (subsN 1 s G)
    ≡ subs s (subn 0 k G)
  e = trans (trans (cong (λ z → subn 0 z (subsN 1 s G)) (sym (subsN0 s k))) (subn-subsN 0 k s G)) (subsN0 s (subn 0 k G))


-- MOVE
#⇛!-mon : {a b : CTerm} {w2 w1 : 𝕎·}
        → w1 ⊑· w2
        → a #⇛! b at w1
        → a #⇛! b at w2
#⇛!-mon {a} {b} {w2} {w1} ext c w' e' = c w' (⊑-trans· ext e')


NATREC-0⇛! : {a b c : Term} {w : 𝕎·}
           → a ⇛! N0 at w
           → NATREC a b c ⇛! b at w
NATREC-0⇛! {a} {b} {c} {w} comp =
  ⇛!-trans {w} {NATREC a b c} {NATREC N0 b c} {b}
    (λ w1 e1 → lift (NATREC⇓ {a} {N0} b c {w1} {w1} (lower (comp w1 e1))))
    (λ w1 e1 → lift (1 , refl))


NATREC-s⇛! : {n : ℕ} {a b c : Term} {w : 𝕎·}
           → a ⇛! NUM (suc n) at w
           → NATREC a b c ⇛! APPLY2 c (NUM n) (NATREC (NUM n) b c) at w
NATREC-s⇛! {n} {a} {b} {c} {w} comp =
  ⇛!-trans {w} {NATREC a b c} {NATREC (NUM (suc n)) b c} {APPLY2 c (NUM n) (NATREC (NUM n) b c)}
    (λ w1 e1 → lift (NATREC⇓ {a} {NUM (suc n)} b c {w1} {w1} (lower (comp w1 e1))))
    (λ w1 e1 → lift (1 , refl))


#NATREC-s⇛! : {n : ℕ} {a b c : CTerm} {w : 𝕎·}
            → a #⇛! #NUM (suc n) at w
            → #NATREC a b c #⇛! #APPLY2 c (#NUM n) (#NATREC (#NUM n) b c) at w
#NATREC-s⇛! {n} {a} {b} {c} {w} comp = NATREC-s⇛! comp


¬namesSub : (s : Sub) → Bool
¬namesSub [] = true
¬namesSub (x ∷ s) = ¬names ⌜ x ⌝ ∧ ¬namesSub s


¬seqSub : (s : Sub) → Bool
¬seqSub [] = true
¬seqSub (x ∷ s) = noseq ⌜ x ⌝ ∧ ¬seqSub s


¬encSub : (s : Sub) → Bool
¬encSub [] = true
¬encSub (x ∷ s) = ¬enc ⌜ x ⌝ ∧ ¬encSub s


¬Names-subn0 : {a b : Term}
             → ¬Names a
             → ¬Names b
             → ¬Names (subn 0 a b)
¬Names-subn0 {a} {b} na nb rewrite sym (sub≡subn a b) = ¬Names-sub {a} {b} na nb


¬Seq-subn0 : {a b : Term}
           → ¬Seq a
           → ¬Seq b
           → ¬Seq (subn 0 a b)
¬Seq-subn0 {a} {b} na nb rewrite sym (sub≡subn a b) = ¬Seq-sub {a} {b} na nb


¬Enc-subn0 : {a b : Term}
           → ¬Enc a
           → ¬Enc b
           → ¬Enc (subn 0 a b)
¬Enc-subn0 {a} {b} na nb rewrite sym (sub≡subn a b) = ¬Enc-sub {a} {b} na nb


→¬Names-subs : (s : Sub) (t : Term)
             → ¬Names t
             → ¬namesSub s ≡ true
             → ¬Names (subs s t)
→¬Names-subs [] t nt ns = nt
→¬Names-subs (x ∷ s) t nt ns = ¬Names-subn0 {⌜ x ⌝} {subs s t} (∧≡true→ₗ _ _ ns) (→¬Names-subs s t nt (∧≡true→ᵣ _ _ ns))


→¬Seq-subs : (s : Sub) (t : Term)
           → ¬Seq t
           → ¬seqSub s ≡ true
           → ¬Seq (subs s t)
→¬Seq-subs [] t nt ns = nt
→¬Seq-subs (x ∷ s) t nt ns = ¬Seq-subn0 {⌜ x ⌝} {subs s t} (∧≡true→ₗ _ _ ns) (→¬Seq-subs s t nt (∧≡true→ᵣ _ _ ns))


→¬Enc-subs : (s : Sub) (t : Term)
           → ¬Enc t
           → ¬encSub s ≡ true
           → ¬Enc (subs s t)
→¬Enc-subs [] t nt ns = nt
→¬Enc-subs (x ∷ s) t nt ns = ¬Enc-subn0 {⌜ x ⌝} {subs s t} (∧≡true→ₗ _ _ ns) (→¬Enc-subs s t nt (∧≡true→ᵣ _ _ ns))


→coveredPI : {s : Sub} {a b : Term}
           → covered s a
           → covered0 s b
           → covered s (PI a b)
→coveredPI {s} {a} {b} ca cb {x} i with ∈-++⁻ (fvars a) i
... | inj₁ j = ca j
... | inj₂ j = cb j


→covered0FUN : {s : Sub} {a b : Term}
             → covered0 s a
             → covered0 s b
             → covered0 s (FUN a b)
→covered0FUN {s} {a} {b} ca cb {x} i
  with ∈-++⁻ (fvars a) (∈lowerVars→ x (fvars a ++ lowerVars (fvars (shiftUp 0 b))) i)
... | inj₁ p = ca (→∈lowerVars x (fvars a) p)
... | inj₂ p
  rewrite fvars-shiftUp≡ 0 b
  with ∈-map⁻ suc (∈lowerVars→ (suc x) (Data.List.map (sucIf≤ 0) (fvars b)) p)
... | v , q , z rewrite suc-injective (sym z) = cb (→∈lowerVars x (fvars b) q)


++⊆₂ : {a b u v w : List Var}
     → a ⊆ u ++ w
     → b ⊆ v ++ w
     → a ++ b ⊆ (u ++ v) ++ w
++⊆₂ {a} {b} {u} {v} {w} s1 s2 {x} i with ∈-++⁻ a i
++⊆₂ {a} {b} {u} {v} {w} s1 s2 {x} i | inj₁ p with ∈-++⁻ u (s1 p)
... | inj₁ q = ∈-++⁺ˡ (∈-++⁺ˡ q)
... | inj₂ q = ∈-++⁺ʳ (u ++ v) q
++⊆₂ {a} {b} {u} {v} {w} s1 s2 {x} i | inj₂ p with ∈-++⁻ v (s2 p)
... | inj₁ q = ∈-++⁺ˡ (∈-++⁺ʳ u q)
... | inj₂ q = ∈-++⁺ʳ (u ++ v) q


++⊆₃ : {a b c u v w x : List Var}
     → a ⊆ u ++ x
     → b ⊆ v ++ x
     → c ⊆ w ++ x
     → a ++ b ++ c ⊆ (u ++ v ++ w) ++ x
++⊆₃ {a} {b} {c} {u} {v} {w} {x} s1 s2 s3 =
  ++⊆₂ {a} {b ++ c} {u} {v ++ w} {x} s1 (++⊆₂ {b} {c} {v} {w} {x} s2 s3)


++⊆₄ : {a b c d u v w x z : List Var}
     → a ⊆ u ++ z
     → b ⊆ v ++ z
     → c ⊆ w ++ z
     → d ⊆ x ++ z
     → a ++ b ++ c ++ d ⊆ (u ++ v ++ w ++ x) ++ z
++⊆₄ {a} {b} {c} {d} {u} {v} {w} {x} {z} s1 s2 s3 s4 =
  ++⊆₂ {a} {b ++ c ++ d} {u} {v ++ w ++ x} {z} s1 (++⊆₃ {b} {c} {d} {v} {w} {x} {z} s2 s3 s4)


lowerVars3++⊆ : (a b : List Var)
              → lowerVars (lowerVars (lowerVars (a ++ b)))
              ⊆ lowerVars (lowerVars (lowerVars a)) ++ lowerVars (lowerVars (lowerVars b))
lowerVars3++⊆ a b {x} i
  rewrite lowerVars++ a b
        | lowerVars++ (lowerVars a) (lowerVars b)
        | lowerVars++ (lowerVars (lowerVars a)) (lowerVars (lowerVars b)) = i


lowerVars3-fvars-shiftUp⊆ : (x : Term)
                          → lowerVars (lowerVars (lowerVars (fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 x))))))
                          ⊆ fvars x
lowerVars3-fvars-shiftUp⊆ x {z} i
  rewrite lowerVars-fvars-shiftUp (shiftUp 0 (shiftUp 0 x))
        | lowerVars-fvars-shiftUp (shiftUp 0 x)
        | lowerVars-fvars-shiftUp x
  = i


fvars-shiftNameUp⊆ : (n : ℕ) (a : Term) → fvars (shiftNameUp n a) ⊆ fvars a
fvars-shiftNameUp⊆ n a rewrite fvars-shiftNameUp n a = ⊆-refl


fvars-subi⊆ : (n : ℕ) (u t : Term) → fvars (subi n u t) ⊆ fvars t ++ fvars u
fvars-subi⊆ n u (VAR x) {z} i with x ≟ n
fvars-subi⊆ n u (VAR x) {z} i | yes p = there i
fvars-subi⊆ n u (VAR x) {z} (here px) | no p = here px
fvars-subi⊆ n u QNAT = λ ()
fvars-subi⊆ n u (LT t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (QLT t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (NUM x) = λ ()
fvars-subi⊆ n u (IFLT t t₁ t₂ t₃) = ++⊆₄ {_} {_} {_} {_} {fvars t} {fvars t₁} {fvars t₂} {fvars t₃} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁) (fvars-subi⊆ n u t₂) (fvars-subi⊆ n u t₃)
fvars-subi⊆ n u (IFEQ t t₁ t₂ t₃) = ++⊆₄ {_} {_} {_} {_} {fvars t} {fvars t₁} {fvars t₂} {fvars t₃} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁) (fvars-subi⊆ n u t₂) (fvars-subi⊆ n u t₃)
fvars-subi⊆ n u (SUC t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (NATREC t t₁ t₂) = ++⊆₃ {_} {_} {_} {fvars t} {fvars t₁} {fvars t₂} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁) (fvars-subi⊆ n u t₂)
fvars-subi⊆ n u (PI t t₁) =
  ++⊆₂ {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))} {fvars t} {lowerVars (fvars t₁)} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (LAMBDA t) =
  ⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t)) (fvars t ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t))
          (⊆-trans (lowerVars++⊆ (fvars t) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u)))
fvars-subi⊆ n u (APPLY t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (FIX t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (LET t t₁) =
  ++⊆₂ {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))} {fvars t} {lowerVars (fvars t₁)} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (WT t t₁ t₂) =
  ++⊆₃
    {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))}
    {fvars (subi n u t₂)} {fvars t} {lowerVars (fvars t₁)} {fvars t₂} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars
               (fvars (subi (suc n) (shiftUp 0 u) t₁))
               (fvars t₁ ++ fvars (shiftUp 0 u))
               (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl (lowerVars-fvars-shiftUp⊆ u))))
    (fvars-subi⊆ n u t₂)
fvars-subi⊆ n u (SUP t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (WREC t t₁) =
  ++⊆₂
    {fvars (subi n u t)} {lowerVars (lowerVars (lowerVars (fvars (subi (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 u))) t₁))))}
    {fvars t} {lowerVars (lowerVars (lowerVars (fvars t₁)))} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars
               (lowerVars (lowerVars (fvars (subi (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 u))) t₁))))
               (lowerVars (lowerVars (fvars t₁ ++ fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 u))))))
               (lowerVars⊆lowerVars
                  (lowerVars (fvars (subi (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 u))) t₁)))
                  (lowerVars (fvars t₁ ++ fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 u)))))
                  (lowerVars⊆lowerVars
                     (fvars (subi (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 u))) t₁))
                     (fvars t₁ ++ fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 u))))
                     (fvars-subi⊆ (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 u))) t₁))))
             (⊆-trans (lowerVars3++⊆ (fvars t₁) (fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 u)))))
                      (⊆-++ {_} {_} {lowerVars (lowerVars (lowerVars (fvars t₁)))}
                         {lowerVars (lowerVars (lowerVars (fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 u))))))}
                         {lowerVars (lowerVars (lowerVars (fvars t₁)))} {fvars u}
                         ⊆-refl (lowerVars3-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (MT t t₁ t₂) =
  ++⊆₃
    {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))}
    {fvars (subi n u t₂)} {fvars t} {lowerVars (fvars t₁)} {fvars t₂} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl (lowerVars-fvars-shiftUp⊆ u))))
    (fvars-subi⊆ n u t₂)
fvars-subi⊆ n u (SUM t t₁) =
  ++⊆₂ {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))} {fvars t} {lowerVars (fvars t₁)} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (PAIR t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (SPREAD t t₁) =
  ++⊆₂
    {fvars (subi n u t)} {lowerVars (lowerVars (fvars (subi (suc (suc n)) (shiftUp 0 (shiftUp 0 u)) t₁)))}
    {fvars t} {lowerVars (lowerVars (fvars t₁))} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars
                  (lowerVars (fvars (subi (suc (suc n)) (shiftUp 0 (shiftUp 0 u)) t₁)))
                  (lowerVars (fvars t₁ ++ fvars (shiftUp 0 (shiftUp 0 u))))
                  (lowerVars⊆lowerVars
                     (fvars (subi (suc (suc n)) (shiftUp 0 (shiftUp 0 u)) t₁))
                     (fvars t₁ ++ fvars (shiftUp 0 (shiftUp 0 u)))
                     (fvars-subi⊆ (suc (suc n)) (shiftUp 0 (shiftUp 0 u)) t₁)))
             (⊆-trans (lowerVars2++⊆ (fvars t₁) (fvars (shiftUp 0 (shiftUp 0 u))))
                      (⊆-++ {_} {_} {lowerVars (lowerVars (fvars t₁))}
                         {lowerVars (lowerVars (fvars (shiftUp 0 (shiftUp 0 u))))}
                         {lowerVars (lowerVars (fvars t₁))} {fvars u}
                         ⊆-refl (lowerVars2-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (SET t t₁) =
  ++⊆₂ {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))} {fvars t} {lowerVars (fvars t₁)} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (TUNION t t₁) =
  ++⊆₂ {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))} {fvars t} {lowerVars (fvars t₁)} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (ISECT t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (UNION t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (INL t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (INR t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (DECIDE t t₁ t₂) =
  ++⊆₃
    {fvars (subi n u t)} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁))} {lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₂))}
    {fvars t} {lowerVars (fvars t₁)} {lowerVars (fvars t₂)} {fvars u}
    (fvars-subi⊆ n u t)
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₁)) (fvars t₁ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₁))
             (⊆-trans (lowerVars++⊆ (fvars t₁) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₁)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₁)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
    (⊆-trans (lowerVars⊆lowerVars (fvars (subi (suc n) (shiftUp 0 u) t₂)) (fvars t₂ ++ fvars (shiftUp 0 u)) (fvars-subi⊆ (suc n) (shiftUp 0 u) t₂))
             (⊆-trans (lowerVars++⊆ (fvars t₂) (fvars (shiftUp 0 u)))
                      (⊆-++ {_} {_} {lowerVars (fvars t₂)} {lowerVars (fvars (shiftUp 0 u))} {lowerVars (fvars t₂)} {fvars u}
                            ⊆-refl
                            (lowerVars-fvars-shiftUp⊆ u))))
fvars-subi⊆ n u (EQ t t₁ t₂) = ++⊆₃ {_} {_} {_} {fvars t} {fvars t₁} {fvars t₂} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁) (fvars-subi⊆ n u t₂)
fvars-subi⊆ n u AX = λ ()
fvars-subi⊆ n u FREE = λ ()
fvars-subi⊆ n u (CS x) = λ ()
fvars-subi⊆ n u (NAME x) = λ ()
fvars-subi⊆ n u (FRESH t) =
  ⊆-trans (fvars-subi⊆ n (shiftNameUp 0 u) t)
          (⊆-++ {_} {_} {fvars t} {fvars (shiftNameUp 0 u)} {fvars t} {fvars u}
            ⊆-refl (fvars-shiftNameUp⊆ 0 u))
fvars-subi⊆ n u (CHOOSE t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u (LOAD t) = λ ()
fvars-subi⊆ n u (MSEQ x) = λ ()
fvars-subi⊆ n u (MAPP x t) = fvars-subi⊆ n u t
fvars-subi⊆ n u NOWRITE = λ ()
fvars-subi⊆ n u NOREAD = λ ()
fvars-subi⊆ n u (SUBSING t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (PARTIAL t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (FFDEFS t t₁) = ++⊆₂ {_} {_} {fvars t} {fvars t₁} {fvars u} (fvars-subi⊆ n u t) (fvars-subi⊆ n u t₁)
fvars-subi⊆ n u PURE = λ ()
fvars-subi⊆ n u NOSEQ = λ ()
fvars-subi⊆ n u NOENC = λ ()
fvars-subi⊆ n u (TERM t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (ENC t) = λ ()
fvars-subi⊆ n u (UNIV x) = λ ()
fvars-subi⊆ n u (LIFT t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (LOWER t) = fvars-subi⊆ n u t
fvars-subi⊆ n u (SHRINK t) = fvars-subi⊆ n u t


→covered0-subi0 : (s : Sub) (t u : Term)
                → covered0 s t
                → covered0 s u
                → covered0 s (subi 0 u t)
→covered0-subi0 s t u covt covu {x} i
  with ∈-++⁻ (fvars t) (fvars-subi⊆ 0 u t {suc x} (∈lowerVars→ x (fvars (subi 0 u t)) i))
... | inj₁ p = covt {x} (→∈lowerVars x (fvars t) p)
... | inj₂ p = covu {x} (→∈lowerVars x (fvars u) p)


→covered0-SUC : (s : Sub) (t : Term)
              → covered0 s t
              → covered0 s (SUC t)
→covered0-SUC s t covt = covt


→covered0-VAR0 : (s : Sub)
               → covered0 s (VAR 0)
→covered0-VAR0 s {x} ()


subs-FST : (s : Sub) (a : Term)
         → subs s (FST a) ≡ FST (subs s a)
subs-FST [] a = refl
subs-FST (x ∷ s) a
  rewrite subs-FST s a
        | #shiftUp 0 x = refl


#subs-FST : (s : Sub) (a : Term) (c : covered s (FST a)) (ca : covered s a)
          → #subs s (FST a) c ≡ #FST (#subs s a ca)
#subs-FST s a c ca = CTerm≡ (subs-FST s a)


coveredFST : {s : Sub} {a : Term}
           → covered s (FST a)
           → covered s a
coveredFST {s} {a} c {x} i = c {x} (∈-++⁺ˡ i)


→coveredFST : {s : Sub} {a : Term}
            → covered s a
            → covered s (FST a)
→coveredFST {s} {a} c {x} i rewrite ++[] (fvars a) = c {x} i


subs-SND : (s : Sub) (a : Term)
         → subs s (SND a) ≡ SND (subs s a)
subs-SND [] a = refl
subs-SND (x ∷ s) a
  rewrite subs-SND s a
        | #shiftUp 0 x = refl


#subs-SND : (s : Sub) (a : Term) (c : covered s (SND a)) (ca : covered s a)
          → #subs s (SND a) c ≡ #SND (#subs s a ca)
#subs-SND s a c ca = CTerm≡ (subs-SND s a)


coveredSND : {s : Sub} {a : Term}
           → covered s (SND a)
           → covered s a
coveredSND {s} {a} c {x} i = c {x} (∈-++⁺ˡ i)


→coveredSND : {s : Sub} {a : Term}
            → covered s a
            → covered s (SND a)
→coveredSND {s} {a} c {x} i rewrite ++[] (fvars a) = c {x} i


→coveredSUM : {s : Sub} {a b : Term}
            → covered s a
            → covered0 s b
            → covered s (SUM a b)
→coveredSUM {s} {a} {b} ca cb {x} i with ∈-++⁻ (fvars a) i
... | inj₁ j = ca j
... | inj₂ j = cb j


length-∷ʳ : {A : Set} (a : A) (l : List A)
          → length (l ∷ʳ a) ≡ suc (length l)
length-∷ʳ {A} a [] = refl
length-∷ʳ {A} a (b ∷ l) = cong suc (length-∷ʳ a l)


{--
≡subs-sym : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H : hypotheses)
          → ≡subs i w s1 s2 H
          → ≡subs i w s2 s1 H
≡subs-sym i w .[] .[] .[] (≡subs[] .i .w) = ≡subs[] i w
≡subs-sym i w .(t1 ∷ s1) .(t2 ∷ s2) .(mkHyp T ∷ hs) (≡subs∷ .i .w t1 t2 s1 s2 T #T hs x h) =
  ≡subs∷ i w t2 t1 s2 s1 T #T hs {!equalInType-sym!} {!!}
 --(≡subs-sym i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs) {!h!})
-- (equalInType-refl x) (≡subs-refl i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs) h)
--}


≡subs→covered0ₗ : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H : hypotheses} {h : hypothesis} {A : Term}
                → ≡subs i w s1 s2 H
                → coveredH (H ∷ʳ h) A
                → covered0 s1 A
≡subs→covered0ₗ {i} {w} {s1} {s2} {H} {h} {A} eqs cov {x} j =
  →∈sdom x s1 q2
  where
  j0 : suc x < length (H ∷ʳ h)
  j0 = ∈hdom→ (cov (∈lowerVars→ x (fvars A) j))

  q0 : length (H ∷ʳ h) ≤ suc (length H)
  q0 rewrite length-∷ʳ h H = ≤-refl

  q1 : x < length H
  q1 = s≤s-inj (≤-trans j0 q0)

  q2 : x < length s1
  q2 rewrite fst (≡subs→length eqs) = q1


≡subs→covered0ᵣ : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H : hypotheses} {h : hypothesis} {A : Term}
                → ≡subs i w s1 s2 H
                → coveredH (H ∷ʳ h) A
                → covered0 s2 A
≡subs→covered0ᵣ {i} {w} {s1} {s2} {H} {h} {A} eqs cov {x} j =
  →∈sdom x s2 q2
  where
  j0 : suc x < length (H ∷ʳ h)
  j0 = ∈hdom→ (cov (∈lowerVars→ x (fvars A) j))

  q0 : length (H ∷ʳ h) ≤ suc (length H)
  q0 rewrite length-∷ʳ h H = ≤-refl

  q1 : x < length H
  q1 = s≤s-inj (≤-trans j0 q0)

  q2 : x < length s2
  q2 rewrite snd (≡subs→length eqs) = q1


subs-ISECT : (s : Sub) (a b : Term)
           → subs s (ISECT a b) ≡ ISECT (subs s a) (subs s b)
subs-ISECT [] a b = refl
subs-ISECT (x ∷ s) a b
  rewrite subs-ISECT s a b
  = refl


subs-NOREAD : (s : Sub)
            → subs s NOREAD ≡ NOREAD
subs-NOREAD [] = refl
subs-NOREAD (x ∷ s)
  rewrite subs-NOREAD s
  = refl


subs-NOWRITE : (s : Sub)
             → subs s NOWRITE ≡ NOWRITE
subs-NOWRITE [] = refl
subs-NOWRITE (x ∷ s)
  rewrite subs-NOWRITE s
  = refl


subs-NOREADMOD : (s : Sub) (a : Term)
               → subs s (NOREADMOD a) ≡ NOREADMOD (subs s a)
subs-NOREADMOD s a =
  trans (subs-ISECT s a NOREAD)
        (cong (ISECT (subs s a)) (subs-NOREAD s))


subs-NOWRITEMOD : (s : Sub) (a : Term)
                → subs s (NOWRITEMOD a) ≡ NOWRITEMOD (subs s a)
subs-NOWRITEMOD s a =
  trans (subs-ISECT s a NOWRITE)
        (cong (ISECT (subs s a)) (subs-NOWRITE s))


subs-SUM! : (s : Sub) (a b : Term)
          → subs s (SUM! a b) ≡ SUM! (subs s a) (subsN 1 s b)
subs-SUM! s a b =
  trans (subs-NOWRITEMOD s (NOREADMOD (SUM a b)))
        (cong NOWRITEMOD (trans (subs-NOREADMOD s (SUM a b))
                                (cong NOREADMOD (subs-SUM s a b))))


coveredNOREADMOD : {s : Sub} {a : Term}
                 → covered s (NOREADMOD a)
                 → covered s a
coveredNOREADMOD {s} {a} c {x} i = c {x} (∈-++⁺ˡ i)


coveredNOWRITEMOD : {s : Sub} {a : Term}
                  → covered s (NOWRITEMOD a)
                  → covered s a
coveredNOWRITEMOD {s} {a} c {x} i = c {x} (∈-++⁺ˡ i)


coveredSUM!₁ : {s : Sub} {a b : Term}
             → covered s (SUM! a b)
             → covered s a
coveredSUM!₁ {s} {a} {b} c =
  coveredSUM₁ {s} {a} {b} (coveredNOREADMOD {s} {SUM a b} (coveredNOWRITEMOD {s} {NOREADMOD (SUM a b)} c))


coveredSUM!₂ : {s : Sub} {a b : Term}
             → covered s (SUM! a b)
             → covered0 s b
coveredSUM!₂ {s} {a} {b} c =
  coveredSUM₂ {s} {a} {b} (coveredNOREADMOD {s} {SUM a b} (coveredNOWRITEMOD {s} {NOREADMOD (SUM a b)} c))


#subs-SUM! : (s : Sub) (a b : Term) (c : covered s (SUM! a b)) (ca : covered s a) (cb : covered0 s b)
           → #subs s (SUM! a b) c ≡ #SUM! (#subs s a ca) (#[0]subs s b cb)
#subs-SUM! s a b c ca cb = CTerm≡ (subs-SUM! s a b)


#subs-SUM!2 : (s : Sub) (a b : Term) (c : covered s (SUM! a b))
            → #subs s (SUM! a b) c ≡ #SUM! (#subs s a (coveredSUM!₁ {s} {a} {b} c)) (#[0]subs s b (coveredSUM!₂ {s} {a} {b} c))
#subs-SUM!2 s a b c = #subs-SUM! s a b c (coveredSUM!₁ {s} {a} {b} c) (coveredSUM!₂ {s} {a} {b} c)


→coveredISECT : {s : Sub} {a b : Term}
              → covered s a
              → covered s b
              → covered s (ISECT a b)
→coveredISECT {s} {a} {b} ca cb {x} i with ∈-++⁻ (fvars a) i
... | inj₁ j = ca j
... | inj₂ j = cb j


→coveredNOREADMOD : {s : Sub} {a : Term}
                  → covered s a
                  → covered s (NOREADMOD a)
→coveredNOREADMOD {s} {a} c = →coveredISECT {s} {a} {NOREAD} c (λ())


→coveredNOWRITEMOD : {s : Sub} {a : Term}
                   → covered s a
                   → covered s (NOWRITEMOD a)
→coveredNOWRITEMOD {s} {a} c = →coveredISECT {s} {a} {NOWRITE} c (λ())


→coveredSUM! : {s : Sub} {a b : Term}
             → covered s a
             → covered0 s b
             → covered s (SUM! a b)
→coveredSUM! {s} {a} {b} ca cb =
  →coveredNOWRITEMOD {s} {NOREADMOD (SUM a b)}
                     (→coveredNOREADMOD {s} {SUM a b} (→coveredSUM {s} {a} {b} ca cb))


covered-subn : (s : Sub) (u F : Term)
             → covered s u
             → covered0 s F
             → covered s (subn 0 u F)
covered-subn s u F covu covF {x} i with ∈-++⁻ (lowerVarsFrom 0 (fvars F)) (fvars-subn⊆ 0 u F {x} i)
covered-subn s u F covu covF {x} i | inj₁ p with ∈lowerVarsFrom→ x 0 (fvars F) p
... | inj₁ (() , p2)
... | inj₂ (p1 , p2) = covF (→∈lowerVars x (fvars F) p2)
covered-subn s u F covu covF {x} i | inj₂ p = covu p


data ≡hypsʳ : ℕ → 𝕎· → Sub → Sub → hypotheses → hypotheses → Set(lsuc L) where
  ≡hypsʳ[] : (i : ℕ) (w : 𝕎·) → ≡hypsʳ i w [] [] [] []
  ≡hypsʳ∷ : (i : ℕ) (w : 𝕎·) (t1 t2 : CTerm) (s1 s2 : Sub)
            (T1 : Term) (c1 : covered s1 T1) (T2 : Term) (c2 : covered s2 T2)
            (hs1 hs2 : hypotheses)
          → equalTypes i w (#subs s1 T1 c1) (#subs s2 T2 c2)
          → ≡hypsʳ i w s1 s2 hs1 hs2
          → ≡hypsʳ i w (s1 ∷ʳ t1) (s2 ∷ʳ t2) (hs1 ∷ʳ mkHyp T1) (hs2 ∷ʳ mkHyp T2)


{--
→≡hypsʳ∷ : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub} {H J : hypotheses} {t1 t2 T1 T2 : CTerm}
         → equalTypes i w T1 T2
         → ≡hypsʳ i w s1 s2 (subHyps 0 ⌜ t1 ⌝ H) (subHyps 0 ⌜ t2 ⌝ J)
         → ≡hypsʳ i w (t1 ∷ s1) (t2 ∷ s2) (mkHyp ⌜ T1 ⌝ ∷ H) (mkHyp ⌜ T2 ⌝ ∷ J)
→≡hypsʳ∷ {i} {w} {s1} {s2} {[]} {[]} {t1} {t2} {T1} {T2} eqt eh = {!!}
→≡hypsʳ∷ {i} {w} {s1} {s2} {[]} {x ∷ J} {t1} {t2} {T1} {T2} eqt eh = {!!}
→≡hypsʳ∷ {i} {w} {s1} {s2} {x ∷ H} {J} {t1} {t2} {T1} {T2} eqt eh = {!!}
--}


{--
→≡hypsʳ : {i : ℕ} {w : 𝕎·} {s1 s2 : Sub } {H J : hypotheses}
         → ≡hyps i w s1 s2 H J
         → ≡hypsʳ i w s1 s2 H J
→≡hypsʳ {i} {w} {.[]} {.[]} {.[]} {.[]} (≡hyps[] .i .w) = ≡hypsʳ[] i w
→≡hypsʳ {i} {w} {.(t1 ∷ s1)} {.(t2 ∷ s2)} {.(mkHyp T1 ∷ hs1)} {.(mkHyp T2 ∷ hs2)} (≡hyps∷ .i .w t1 t2 s1 s2 T1 #T1 T2 #T2 hs1 hs2 x eh) =
  {!!}
  where
  ind : ≡hypsʳ i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs1) (subHyps 0 ⌜ t2 ⌝ hs2)
  ind = →≡hypsʳ eh
--}


{--
≡hyps∷ʳ→ : (i : Nat) (w : 𝕎·) (s1 s2 : Sub) (H J : hypotheses) (A B : BTerm)
         → ≡hyps i w s1 s2 (H Data.List.∷ʳ (mkHyp A)) (J Data.List.∷ʳ (mkHyp B))
         → Σ CTerm (λ t1 →
           Σ CTerm (λ t2 →
           Σ Sub (λ ss1 →
           Σ Sub (λ ss2 →
           Σ (covered ss1 A) (λ cA →
           Σ (covered ss2 B) (λ cB →
           s1 ≣ ss1 Data.List.∷ʳ t1
         × s2 ≣ ss2 Data.List.∷ʳ t2
         × ≡hyps i w ss1 ss2 H J
         × equalTypes i w (#subs ss1 A cA) (#subs ss2 B cB)))))))
≡hyps∷ʳ→ i w s1 s2 H J A B eh = {!!}
--}


#→covered : {A : Term} → # A → covered [] A
#→covered {A} ca {x} rewrite ca = λ ()


#subs-[] : {A : Term} (ca : # A)
          → #subs [] A (#→covered {A} ca)
          ≡ ct A ca
#subs-[] {A} ca = CTerm≡ refl


subHyps++ : (n : ℕ) (t : Term) (H J : hypotheses)
          → subHyps n t (H ++ J)
          ≡ subHyps n t H ++ subHyps (length H + n) t J
subHyps++ n t [] J = refl
subHyps++ n t (x ∷ H) J =
  cong (λ z → (mkHyp (subn n t (hypothesis.hyp x))) ∷ z)
       (trans (subHyps++ (suc n) t H J)
               (cong (λ z → subHyps (suc n) t H ++ subHyps z t J)
                     (+-suc (length H) n)))


→∈lowerVarsFrom₁ : (x n : Var) (l : List Var)
                 → n ≤ x
                 → suc x ∈ l
                 → x ∈ lowerVarsFrom n l
→∈lowerVarsFrom₁ x n (0 ∷ l) nlex (there slel) with n ≟ 0
... | yes p = →∈lowerVarsFrom₁ x n l nlex slel
... | no p = there (→∈lowerVarsFrom₁ x n l nlex slel)
→∈lowerVarsFrom₁ x n (suc x₁ ∷ l) nlex (here px) rewrite sym (suc-injective px) with suc x <? n
... | yes p = ⊥-elim (<-irrefl refl (≤-trans (<⇒≤ p) nlex))
... | no p with n ≟ suc x
... | yes q rewrite q = ⊥-elim (<-irrefl refl nlex)
... | no q = here refl
→∈lowerVarsFrom₁ x n (suc x₁ ∷ l) nlex (there slel) with suc x₁ <? n
... | yes p = there (→∈lowerVarsFrom₁ x n l nlex slel)
... | no p with n ≟ suc x₁
... | yes q rewrite q = →∈lowerVarsFrom₁ x (suc x₁) l nlex slel
... | no q = there (→∈lowerVarsFrom₁ x n l nlex slel)


covered-subn→covered-cons : (s : Sub) (t : Term) (u : CTerm) (A : Term)
                          → covered s (subn (length s) t A)
                          → covered (u ∷ s) A
covered-subn→covered-cons s t u A cov {0} i = here refl
covered-subn→covered-cons s t u A cov {suc x} i =
  there (∈-map⁺ suc c)
  where
  c : x ∈ sdom s
  c with x <? length s
  ... | yes p = →∈sdom x s p
  ... | no p = cov {x} (⊆fvars-subn (length s) t A (→∈lowerVarsFrom₁ x (length s) (fvars A) (≮⇒≥ p) i))


covered-subn→covered-cons₂ : (n : ℕ) (s : Sub) (t : Term) (u : CTerm) (A : Term)
                            → n ≡ length s
                            → covered s (subn n t A)
                            → covered (u ∷ s) A
covered-subn→covered-cons₂ n s t u A refl cov = covered-subn→covered-cons s t u A cov


≡hyps∷ʳ→ : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H J : hypotheses) (A B : Term)
         → ≡hyps i w s1 s2 (H ∷ʳ (mkHyp A)) (J ∷ʳ (mkHyp B))
         → Σ CTerm (λ t1 →
           Σ CTerm (λ t2 →
           Σ Sub (λ ss1 →
           Σ Sub (λ ss2 →
           Σ (covered ss1 A) (λ cA →
           Σ (covered ss2 B) (λ cB →
           s1 ≡ ss1 ∷ʳ t1
         × s2 ≡ ss2 ∷ʳ t2
         × ≡hyps i w ss1 ss2 H J
         × equalTypes i w (#subs ss1 A cA) (#subs ss2 B cB)))))))
≡hyps∷ʳ→ i w [] [] [] J A B ()
≡hyps∷ʳ→ i w [] [] (x ∷ H) J A B ()
≡hyps∷ʳ→ i w (x ∷ []) (x₁ ∷ []) [] [] A B (≡hyps∷ .i .w .x .x₁ .[] .[] .A #T1 .B #T2 .[] .[] x₂ (≡hyps[] .i .w)) =
  x , x₁ , [] , [] , #→covered {A} #T1 , #→covered {B} #T2 , refl , refl , ≡hyps[] i w ,
  ≡CTerm→eqTypes (sym (#subs-[] {A} #T1)) (sym (#subs-[] {B} #T2)) x₂
≡hyps∷ʳ→ i w (x ∷ []) (x₁ ∷ x₂ ∷ s2) [] [] A B (≡hyps∷ .i .w .x .x₁ .[] .(x₂ ∷ s2) .A #T1 .B #T2 .[] .[] x₃ ())
≡hyps∷ʳ→ i w (x ∷ x₂ ∷ s1) (x₃ ∷ s2) [] [] A B (≡hyps∷ .i .w .x .x₃ .(x₂ ∷ s1) .s2 .A #T1 .B #T2 .[] .[] x₁ ())
≡hyps∷ʳ→ i w (x ∷ s1) (x₁ ∷ s2) [] (.(mkHyp T2) ∷ []) A B (≡hyps∷ .i .w .x .x₁ .s1 .s2 .A #T1 T2 #T2 .[] .([] ++ [ mkHyp B ]) x₂ ())
≡hyps∷ʳ→ i w (x ∷ s1) (x₁ ∷ s2) [] (.(mkHyp T2) ∷ (x₃ ∷ J)) A B (≡hyps∷ .i .w .x .x₁ .s1 .s2 .A #T1 T2 #T2 .[] .(x₃ ∷ J ++ [ mkHyp B ]) x₂ ())
≡hyps∷ʳ→ i w (x ∷ s1) (x₁ ∷ s2) (.(mkHyp T1) ∷ []) [] A B (≡hyps∷ .i .w .x .x₁ .s1 .s2 T1 #T1 .B #T2 .([] ++ [ mkHyp A ]) .[] x₂ ())
≡hyps∷ʳ→ i w (x ∷ s1) (x₁ ∷ s2) (.(mkHyp T1) ∷ (x₃ ∷ H)) [] A B (≡hyps∷ .i .w .x .x₁ .s1 .s2 T1 #T1 .B #T2 .(x₃ ∷ H ++ [ mkHyp A ]) .[] x₂ ())
≡hyps∷ʳ→ i w (x ∷ s1) (x₁ ∷ s2) (.(mkHyp T1) ∷ H) (.(mkHyp T2) ∷ J) A B (≡hyps∷ .i .w .x .x₁ .s1 .s2 T1 #T1 T2 #T2 .(H ++ [ mkHyp A ]) .(J ++ [ mkHyp B ]) x₂ eh)
  rewrite subHyps++ 0 ⌜ x  ⌝ H ((mkHyp A) ∷ [])
        | subHyps++ 0 ⌜ x₁ ⌝ J ((mkHyp B) ∷ [])
  with ≡hyps∷ʳ→ i w s1 s2 (subHyps 0 ⌜ x ⌝ H) (subHyps 0 ⌜ x₁ ⌝ J)
                (subn (length H + 0) ⌜ x ⌝ A) (subn (length J + 0) ⌜ x₁ ⌝ B)
                eh
... | t1 , t2 , ss1 , ss2 , cA , cB , e1 , e2 , eH , eT =  -- now by induction
  t1 , t2 , x ∷ ss1 , x₁ ∷ ss2 , cA' , cB' ,
  cong (λ z → x ∷ z) e1 , cong (λ z → x₁ ∷ z) e2 ,
  ≡hyps∷ i w x x₁ ss1 ss2 T1 #T1 T2 #T2 H J x₂ eH ,
  eTx
    where
    cA' : covered (x ∷ ss1) A
    cA' = covered-subn→covered-cons₂
            (length H + 0) ss1 ⌜ x ⌝ x A
            (trans (+0 (length H)) (trans (sym (length-subHyps 0 ⌜ x ⌝ H)) (sym (fst (≡hyps→length eH)))))
            cA

    cB' : covered (x₁ ∷ ss2) B
    cB' = covered-subn→covered-cons₂
            (length J + 0) ss2 ⌜ x₁ ⌝ x₁ B
            (trans (+0 (length J)) (trans (sym (length-subHyps 0 ⌜ x₁ ⌝ J)) (sym (fst (snd (≡hyps→length eH))))))
            cB

    eT' : equalTypes i w (#subs ss1 (subn (length H + 0) ⌜ x ⌝ A) cA) (#subs ss2 (subn (length J + 0) ⌜ x₁ ⌝ B) cB)
    eT' = eT

    eq1 : subs ss1 (subn (length H + 0) ⌜ x ⌝ A) ≡ subs (x ∷ ss1) A
    eq1 rewrite trans (+0 (length H)) (trans (sym (length-subHyps 0 ⌜ x ⌝ H)) (sym (fst (≡hyps→length eH)))) =
      sym (subn-subs 0 ⌜ x ⌝ (CTerm.closed x) ss1 A)

    eq2 : subs ss2 (subn (length J + 0) ⌜ x₁ ⌝ B) ≡ subs (x₁ ∷ ss2) B
    eq2 rewrite trans (+0 (length J)) (trans (sym (length-subHyps 0 ⌜ x₁ ⌝ J)) (sym (fst (snd (≡hyps→length eH))))) =
      sym (subn-subs 0 ⌜ x₁ ⌝ (CTerm.closed x₁) ss2 B)

    eTx : equalTypes i w (#subs (x ∷ ss1) A cA') (#subs (x₁ ∷ ss2) B cB')
    eTx = ≡CTerm→eqTypes (CTerm≡ eq1) (CTerm≡ eq2) eT'


≡subs∷ʳ→ : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (H : hypotheses) (A : Term)
         → ≡subs i w s1 s2 (H ∷ʳ (mkHyp A))
         → Σ CTerm (λ t1 →
           Σ CTerm (λ t2 →
           Σ Sub (λ ss1 →
           Σ Sub (λ ss2 →
           Σ (covered ss1 A) (λ cA →
           s1 ≡ ss1 ∷ʳ t1
         × s2 ≡ ss2 ∷ʳ t2
         × ≡subs i w ss1 ss2 H
         × equalInType i w (#subs ss1 A cA) t1 t2)))))
≡subs∷ʳ→ i w [] [] [] A ()
≡subs∷ʳ→ i w [] [] (x ∷ H) A ()
≡subs∷ʳ→ i w (x ∷ []) (x₁ ∷ []) [] A (≡subs∷ .i .w .x .x₁ .[] .[] .A #T .[] x₂ (≡subs[] .i .w)) =
  x , x₁ , [] , [] , #→covered {A} #T , refl , refl , ≡subs[] i w , ≡CTerm→equalInType (sym (#subs-[] {A} #T)) x₂
≡subs∷ʳ→ i w (x ∷ []) (x₁ ∷ x₂ ∷ s2) [] A (≡subs∷ .i .w .x .x₁ .[] .(x₂ ∷ s2) .A #T .[] x₃ ())
≡subs∷ʳ→ i w (x₁ ∷ x₂ ∷ s1) (x₃ ∷ s2) [] A (≡subs∷ .i .w .x₁ .x₃ .(x₂ ∷ s1) .s2 .A #T .[] x ())
≡subs∷ʳ→ i w (x ∷ s1) (x₁ ∷ s2) (.(mkHyp T) ∷ H) A (≡subs∷ .i .w .x .x₁ .s1 .s2 T #T .(H ++ [ mkHyp A ]) x₂ es)
  rewrite subHyps++ 0 ⌜ x  ⌝ H ((mkHyp A) ∷ [])
  with ≡subs∷ʳ→ i w s1 s2 (subHyps 0 ⌜ x ⌝ H) (subn (length H + 0) ⌜ x ⌝ A) es
... | t1 , t2 , ss1 , ss2 , cA , e1 , e2 , eS , eT =  -- now by induction
  t1 , t2 , x ∷ ss1 , x₁ ∷ ss2 , cA' ,
  cong (λ z → x ∷ z) e1 , cong (λ z → x₁ ∷ z) e2 ,
  ≡subs∷ i w x x₁ ss1 ss2 T #T H x₂ eS ,
  eTx
    where
    cA' : covered (x ∷ ss1) A
    cA' = covered-subn→covered-cons₂
            (length H + 0) ss1 ⌜ x ⌝ x A
            (trans (+0 (length H)) (trans (sym (length-subHyps 0 ⌜ x ⌝ H)) (sym (fst (≡subs→length eS)))))
            cA

    eq1 : subs ss1 (subn (length H + 0) ⌜ x ⌝ A) ≡ subs (x ∷ ss1) A
    eq1 rewrite trans (+0 (length H)) (trans (sym (length-subHyps 0 ⌜ x ⌝ H)) (sym (fst (≡subs→length eS)))) =
      sym (subn-subs 0 ⌜ x ⌝ (CTerm.closed x) ss1 A)

    eTx : equalInType i w (#subs (x ∷ ss1) A cA') t1 t2
    eTx = ≡CTerm→equalInType (CTerm≡ eq1) eT


≡subs∷ʳ→₂ : (i : ℕ) (w : 𝕎·) (s1 s2 : Sub) (t1 t2 : CTerm) (H : hypotheses) (A : Term)
          → ≡subs i w (s1 ∷ʳ t1) (s2 ∷ʳ t2) (H ∷ʳ (mkHyp A))
          → Σ (covered s1 A) (λ cA → ≡subs i w s1 s2 H
            × equalInType i w (#subs s1 A cA) t1 t2)
≡subs∷ʳ→₂ i w s1 s2 t1 t2 H A es
  with ≡subs∷ʳ→ i w (s1 ∷ʳ t1) (s2 ∷ʳ t2) H A es
... | t1 , t2 , ss1 , ss2 , cA , e1 , e2 , eS , eT
  rewrite fst (∷ʳ-injective s1 ss1 e1)
        | snd (∷ʳ-injective s1 ss1 e1)
        | fst (∷ʳ-injective s2 ss2 e2)
        | snd (∷ʳ-injective s2 ss2 e2)
  = cA , eS , eT


subs∷ʳ-shiftUp : (s : Sub) (t : CTerm) (u : Term)
               → subs (s ∷ʳ t) (shiftUp 0 u)
               ≡ subs s u
subs∷ʳ-shiftUp [] t u = trans (sym (sub≡subn ⌜ t ⌝ (shiftUp 0 u))) (sub-shiftUp0≡ ⌜ t ⌝ u)
subs∷ʳ-shiftUp (x ∷ s) t u = cong (subn 0 ⌜ x ⌝) (subs∷ʳ-shiftUp s t u)


sub-CTerm : (x t : CTerm)
          → sub ⌜ x ⌝ ⌜ t ⌝ ≡ ⌜ t ⌝
sub-CTerm x t
  rewrite #shiftUp 0 t | #subv 0 (shiftUp 0 ⌜ x ⌝) ⌜ t ⌝ (CTerm.closed t) | #shiftDown 0 t = refl


subs∷ʳ-VAR0 : (s : Sub) (t : CTerm)
            → subs (s ∷ʳ t) (VAR 0) ≡ ⌜ t ⌝
subs∷ʳ-VAR0 [] t = refl
subs∷ʳ-VAR0 (x ∷ s) t
  rewrite subs∷ʳ-VAR0 s t
  = trans (sym (sub≡subn ⌜ x ⌝ ⌜ t ⌝)) (sub-CTerm x t)


covered∷ʳ-shiftUp→ : (s : Sub) (t : CTerm) (A : Term)
                   → covered (s ∷ʳ t) (shiftUp 0 A)
                   → covered s A
covered∷ʳ-shiftUp→ s t A cov {x} i = c5 c4
  where
  c1 : suc x ∈ Data.List.map (sucIf≤ 0) (fvars A)
  c1 = ∈-map⁺ suc i

  c2 : suc x ∈ fvars (shiftUp 0 A)
  c2 = subst (λ z → suc x ∈ z) (sym (fvars-shiftUp≡ 0 A)) c1

  c3 : suc x ∈ sdom (s ∷ʳ t)
  c3 = cov {suc x} c2

  c4 : suc x ∈ 0 ∷ raiseVars (sdom s)
  c4 = subst (λ z → suc x ∈ z) (sdom∷ʳ s t) c3

  c5 : suc x ∈ 0 ∷ raiseVars (sdom s)
    → x ∈ sdom s
  c5 (there h) = ∈raiseVars→ {x} {sdom s} h


-- MOVE
→equalInType-EQ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                  → equalInType u w A a b
                  → equalInType u w (#EQ a b A) f g
→equalInType-EQ {u} {w} {a} {b} {A} {f} {g} a∈ =
  equalInType-EQ
    (fst a∈)
    (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon a∈ w1 e1))


-- MOVE
SUC⇛! : {w : 𝕎·} {a : Term} {k : ℕ}
      → a ⇛! NUM k at w
      → SUC a ⇛! NUM (ℕ.suc k) at w
SUC⇛! {w} {a} {k} comp w1 e1 =
  lift (⇓NUM→SUC⇓NUM {a} {k} {w1} {w1} (lower (comp w1 e1)))


-- MOVE
SUC∈NAT! : {i : ℕ} {w : 𝕎·} {a b : CTerm}
         → equalInType i w #NAT! a b
         → equalInType i w #NAT! (#SUC a) (#SUC b)
SUC∈NAT! {i} {w} {a} {b} h =
  →equalInType-NAT! i w (#SUC a) (#SUC b) (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w a b h))
  where
  aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                     → #⇛!sameℕ w' (#SUC a) (#SUC b))
  aw w1 e1 (k , c₁ , c₂) = ℕ.suc k , SUC⇛! c₁ , SUC⇛! c₂


→coveredPAIR : {s : Sub} {a b : Term}
             → covered s a
             → covered s b
             → covered s (PAIR a b)
→coveredPAIR {s} {a} {b} ca cb {x} i with ∈-++⁻ (fvars a) i
... | inj₁ j = ca j
... | inj₂ j = cb j


→coveredAPPLY : {s : Sub} {a b : Term}
              → covered s a
              → covered s b
              → covered s (APPLY a b)
→coveredAPPLY {s} {a} {b} ca cb {x} i with ∈-++⁻ (fvars a) i
... | inj₁ j = ca j
... | inj₂ j = cb j

\end{code}
