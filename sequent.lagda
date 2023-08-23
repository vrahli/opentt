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
open import Relation.Binary.PropositionalEquality using (sym ; subst ; cong)
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
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import subst(W)(C)(K)(G)(X)(N)(EC)


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


covered : (s : Sub) (t : Term) → Set
covered s t = fvars t ⊆ sdom s


subsN : (n : ℕ) (s : Sub) (t : Term) → Term
subsN n [] t = t
subsN n (u ∷ s) t = subn n ⌜ u ⌝ (subsN n s t)


subs : (s : Sub) (t : Term) → Term
subs [] t = t
subs (u ∷ s) t = subn 0 ⌜ u ⌝ (subs s t)


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


validEq : (n : ℕ) (w : 𝕎·) (H : hypotheses) (a b T : Term) → Set(lsuc(L))
validEq n w H a b T = sequent_pairwise_true n w (mkEqSeq H a b T)


validMem : (n : ℕ) (w : 𝕎·) (H : hypotheses) (a T : Term) → Set(lsuc(L))
validMem n w H a T = sequent_pairwise_true n w (mkSeq H T a)


-- More properties about subs

subs-NAT! : (s : Sub)
          → subs s NAT! ≡ NAT!
subs-NAT! [] = refl
subs-NAT! (x ∷ s) rewrite subs-NAT! s = refl


#subs-NAT! : (s : Sub) (c : covered s NAT!)
           → #subs s NAT! c ≡ #NAT!
#subs-NAT! s c = CTerm≡ (subs-NAT! s)


subs-UNIV : (s : Sub) (i : ℕ)
          → subs s (UNIV i) ≡ UNIV i
subs-UNIV [] i = refl
subs-UNIV (x ∷ s) i rewrite subs-UNIV s i = refl


#subs-UNIV : (s : Sub) (i : ℕ) (c : covered s (UNIV i))
           → #subs s (UNIV i) c ≡ #UNIV i
#subs-UNIV s i c = CTerm≡ (subs-UNIV s i)


covered0 : (s : Sub) (t : Term) → Set
--covered0 s t = fvars t ⊆ raiseVars (sdom s)
covered0 s t = lowerVars (fvars t) ⊆ sdom s


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


#subs-PI : (s : Sub) (a b : Term) (c : covered s (PI a b)) (ca : covered s a) (cb : covered0 s b)
         → #subs s (PI a b) c ≡ #PI (#subs s a ca) (#[0]subs s b cb)
#subs-PI s a b c ca cb = CTerm≡ (subs-PI s a b)


#subs-PI2 : (s : Sub) (a b : Term) (c : covered s (PI a b))
          → #subs s (PI a b) c ≡ #PI (#subs s a (coveredPI₁ {s} {a} {b} c)) (#[0]subs s b (coveredPI₂ {s} {a} {b} c))
#subs-PI2 s a b c = #subs-PI s a b c (coveredPI₁ {s} {a} {b} c) (coveredPI₂ {s} {a} {b} c)

\end{code}
