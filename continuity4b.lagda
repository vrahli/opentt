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
open import choiceBar
open import encode


module continuity4b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                    (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)



↓vars++ : (a b : List Var) → ↓vars (a ++ b) ≡ ↓vars a ++ ↓vars b
↓vars++ [] b = refl
↓vars++ (0 ∷ a) b rewrite ↓vars++ a b = refl
↓vars++ (suc x ∷ a) b rewrite ↓vars++ a b = refl


→∈↓vars-map-suc : (v : Name) (l : List Name)
                   → v ∈ l
                   → v ∈ ↓vars (Data.List.map suc l)
→∈↓vars-map-suc v [] i = i
→∈↓vars-map-suc v (x ∷ l) (here px) = here px
→∈↓vars-map-suc v (x ∷ l) (there i) = there (→∈↓vars-map-suc v l i)


→↓vars-names-testMup-F : (v : Name) (F f : Term)
                          → v ∈ names F
                          → v ∈ ↓vars (names (testMup 0 F f))
→↓vars-names-testMup-F v F f i
  rewrite names-shiftUp 0 (shiftNameUp 0 F)
        | names-shiftUp 3 (shiftUp 0 (shiftNameUp 0 f))
        | names-shiftUp 0 (shiftNameUp 0 f)
        | ↓vars++ (names (shiftNameUp 0 F) ++ 0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ []) [ 0 ]
        | ↓vars++ (names (shiftNameUp 0 F)) (0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ []) =
  there (∈-++⁺ˡ (∈-++⁺ˡ j))
  where
    j : v ∈ ↓vars (names (shiftNameUp 0 F))
    j rewrite names-shiftNameUp≡ 0 F = →∈↓vars-map-suc v (names F) i


→↓vars-names-testMup-f : (v : Name) (F f : Term)
                          → v ∈ names f
                          → v ∈ ↓vars (names (testMup 0 F f))
→↓vars-names-testMup-f v F f i
  rewrite names-shiftUp 0 (shiftNameUp 0 F)
        | names-shiftUp 3 (shiftUp 0 (shiftNameUp 0 f))
        | names-shiftUp 0 (shiftNameUp 0 f)
        | ↓vars++ (names (shiftNameUp 0 F) ++ 0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ []) [ 0 ]
        | ↓vars++ (names (shiftNameUp 0 F)) (0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ [])
        | ++[] (names (shiftNameUp 0 f)) =
  there (∈-++⁺ˡ (∈-++⁺ʳ (↓vars (names (shiftNameUp 0 F))) (there (there j))))
  where
    j : v ∈ ↓vars (names (shiftNameUp 0 f))
    j rewrite names-shiftNameUp≡ 0 f = →∈↓vars-map-suc v (names f) i



¬newChoiceT-testMup∈names-F : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMup 0 F f)) ∈ names F
¬newChoiceT-testMup∈names-F w F f i = q (→↓vars-names-testMup-F (newChoiceT w (testMup 0 F f)) F f i)
  where
    q : ¬ (newChoiceT w (testMup 0 F f)) ∈ ↓vars (names (testMup 0 F f))
    q = λ x → snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMup 0 F f)))) (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ʳ (names𝕎· w) x))



¬newChoiceT-testMup∈names-f : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMup 0 F f)) ∈ names f
¬newChoiceT-testMup∈names-f w F f i = q (→↓vars-names-testMup-f (newChoiceT w (testMup 0 F f)) F f i)
  where
    q : ¬ (newChoiceT w (testMup 0 F f)) ∈ ↓vars (names (testMup 0 F f))
    q = λ x → snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMup 0 F f)))) (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ʳ (names𝕎· w) x))


¬newChoiceT-testMup∈names𝕎 : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMup 0 F f)) ∈ names𝕎· w
¬newChoiceT-testMup∈names𝕎 w F f i =
  snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMup 0 F f))))
      (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ˡ i))


ren : Set
ren = List (Name × Name)


sren : ren → ren
sren [] = []
sren ((a , b) ∷ r) = (suc a , suc b) ∷ sren r


renₗ : ren → List Name
renₗ [] = []
renₗ ((a , b) ∷ r) = a ∷ renₗ r


renᵣ : ren → List Name
renᵣ [] = []
renᵣ ((a , b) ∷ r) = b ∷ renᵣ r


names∈ren : Name → Name → ren → Set
names∈ren name1 name2 [] = name1 ≡ name2
names∈ren name1 name2 ((a , b) ∷ r) =
  (name1 ≡ a × name2 ≡ b)
  ⊎ (¬ name1 ≡ a × ¬ name2 ≡ b × names∈ren name1 name2 r)


{--
names∈ren : Name → Name → ren → Set
names∈ren name1 name2 r =
  (name1 ≡ name2 × ¬ name1 ∈ renₗ r × ¬ name2 ∈ renᵣ r)
  ⊎ (name1 , name2) ∈ r
--}



{--
names∈ren-refl : (x : Name) (r : ren) → names∈ren x x r
names∈ren-refl x r = inj₁ refl
--}


sym-ren : ren → ren
sym-ren [] = []
sym-ren ((a , b) ∷ r) = (b , a) ∷ sym-ren r


∈sym-ren : {a b : Name} {r : ren} → (a , b) ∈ r → (b , a) ∈ sym-ren r
∈sym-ren {a} {b} {[]} ()
∈sym-ren {a} {b} {(u , v) ∷ r} (here px)
  rewrite pair-inj₁ px | pair-inj₂ px = here refl
∈sym-ren {a} {b} {(u , v) ∷ r} (there i) = there (∈sym-ren i)


sym-ren-idem : (r : ren) → sym-ren (sym-ren r) ≡ r
sym-ren-idem [] = refl
sym-ren-idem ((a , b) ∷ r) rewrite sym-ren-idem r = refl


{--
names∈ren-sym : {n1 n2 : Name} {r : ren} → names∈ren n1 n2 r → names∈ren n2 n1 (sym-ren r)
names∈ren-sym {n1} {n2} {r} (inj₁ x) rewrite x = inj₁ refl
names∈ren-sym {n1} {n2} {r} (inj₂ i) = inj₂ (∈sym-ren i)
--}


{--
names∈ren-sym→ : {n1 n2 : Name} {r : ren} → names∈ren n1 n2 (sym-ren r) → names∈ren n2 n1 r
names∈ren-sym→ {n1} {n2} {r} i = c2
  where
    c2 : names∈ren n2 n1 r
    c2 rewrite sym (sym-ren-idem r) = names∈ren-sym c1
      where
        c1 : names∈ren n1 n2 (sym-ren r)
        c1  rewrite sym-ren-idem r = i
--}


data updRel2 (name : Name) (f g : Term) (r : ren) : Term → Term → Set where
  updRel2-VAR     : (x : Var) → updRel2 name f g r (VAR x) (VAR x)
  updRel2-NAT     : updRel2 name f g r NAT NAT
  updRel2-QNAT    : updRel2 name f g r QNAT QNAT
  updRel2-TNAT    : updRel2 name f g r TNAT TNAT
  updRel2-LT      : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (LT a₁ b₁) (LT a₂ b₂)
  updRel2-QLT     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (QLT a₁ b₁) (QLT a₂ b₂)
  updRel2-NUM     : (x : ℕ) → updRel2 name f g r (NUM x) (NUM x)
  updRel2-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r c₁ c₂ → updRel2 name f g r d₁ d₂ → updRel2 name f g r (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  updRel2-IFEQ    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r c₁ c₂ → updRel2 name f g r d₁ d₂ → updRel2 name f g r (IFEQ a₁ b₁ c₁ d₁) (IFEQ a₂ b₂ c₂ d₂)
  updRel2-SUC     : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (SUC a₁) (SUC a₂)
  updRel2-PI      : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (PI a₁ b₁) (PI a₂ b₂)
  updRel2-LAMBDA  : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (LAMBDA a₁) (LAMBDA a₂)
  updRel2-APPLY   : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (APPLY a₁ b₁) (APPLY a₂ b₂)
  updRel2-MSEQ    : (s : 𝕊) → updRel2 name f g r (MSEQ s) (MSEQ s)
  updRel2-MAPP    : (s : 𝕊) (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (MAPP s a₁) (MAPP s a₂)
  updRel2-FIX     : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (FIX a₁) (FIX a₂)
  updRel2-LET     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (LET a₁ b₁) (LET a₂ b₂)
  updRel2-SUM     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (SUM a₁ b₁) (SUM a₂ b₂)
  updRel2-PAIR    : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (PAIR a₁ b₁) (PAIR a₂ b₂)
  updRel2-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  updRel2-WT      : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (WT a₁ b₁) (WT a₂ b₂)
  updRel2-SUP     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (SUP a₁ b₁) (SUP a₂ b₂)
  updRel2-WREC    : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (WREC a₁ b₁) (WREC a₂ b₂)
  updRel2-MT      : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (MT a₁ b₁) (MT a₂ b₂)
  updRel2-SET     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (SET a₁ b₁) (SET a₂ b₂)
  updRel2-ISECT   : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (ISECT a₁ b₁) (ISECT a₂ b₂)
  updRel2-TUNION  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (TUNION a₁ b₁) (TUNION a₂ b₂)
  updRel2-UNION   : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (UNION a₁ b₁) (UNION a₂ b₂)
  updRel2-QTUNION : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  updRel2-INL     : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (INL a₁) (INL a₂)
  updRel2-INR     : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (INR a₁) (INR a₂)
  updRel2-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r c₁ c₂ → updRel2 name f g r (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  updRel2-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r c₁ c₂ → updRel2 name f g r (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  updRel2-EQB      : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r c₁ c₂ → updRel2 name f g r d₁ d₂ → updRel2 name f g r (EQB a₁ b₁ c₁ d₁) (EQB a₂ b₂ c₂ d₂)
  updRel2-AX      : updRel2 name f g r AX AX
  updRel2-FREE    : updRel2 name f g r FREE FREE
  updRel2-CS      : (name1 name2 : Name) → ¬ name1 ≡ name → ¬ name2 ≡ name → names∈ren name1 name2 r → updRel2 name f g r (CS name1) (CS name2)
  updRel2-NAME    : (name1 name2 : Name) → ¬ name1 ≡ name → ¬ name2 ≡ name → names∈ren name1 name2 r → updRel2 name f g r (NAME name1) (NAME name2)
  updRel2-FRESH   : (a b : Term) → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) (sren r) a b → updRel2 name f g r (FRESH a) (FRESH b)
  updRel2-LOAD    : (a : Term) → updRel2 name f g r (LOAD a) (LOAD a)
  updRel2-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  updRel2-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel2 name1 name2 f a₁ a₂ → updRel2 name1 name2 f b₁ b₂ → updRel2 name1 name2 f c₁ c₂ → updRel2 name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updRel2-TSQUASH : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (TSQUASH a₁) (TSQUASH a₂)
  updRel2-TTRUNC  : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (TTRUNC a₁) (TTRUNC a₂)
  updRel2-TCONST  : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (TCONST a₁) (TCONST a₂)
  updRel2-SUBSING : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (SUBSING a₁) (SUBSING a₂)
  updRel2-PURE    : updRel2 name f g r PURE PURE
  updRel2-NOSEQ   : updRel2 name f g r NOSEQ NOSEQ
  updRel2-TERM    : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (TERM a₁) (TERM a₂)
  updRel2-ENC     : (a : Term) → updRel2 name f g r a a → updRel2 name f g r (ENC a) (ENC a)
  updRel2-DUM     : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (DUM a₁) (DUM a₂)
  updRel2-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r b₁ b₂ → updRel2 name f g r (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  updRel2-UNIV    : (x : ℕ) → updRel2 name f g r (UNIV x) (UNIV x)
  updRel2-LIFT    : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (LIFT a₁) (LIFT a₂)
  updRel2-LOWER   : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (LOWER a₁) (LOWER a₂)
  updRel2-SHRINK  : (a₁ a₂ : Term) → updRel2 name f g r a₁ a₂ → updRel2 name f g r (SHRINK a₁) (SHRINK a₂)
  updRel2-upd     : updRel2 name f g r (upd name f) (force g)



{--
sameRes-refl : (w : 𝕎·) → sameRes w w
sameRes-refl w name r = (λ x → x) , (λ x → x)


sameRes-sym : {w1 w2 : 𝕎·} → sameRes w1 w2 → sameRes w2 w1
sameRes-sym {w1} {w2} sres name r = snd (sres name r) , fst (sres name r)


sameRes-trans : {w1 w2 w3 : 𝕎·} → sameRes w1 w2 → sameRes w2 w3 → sameRes w1 w3
sameRes-trans {w1} {w2} {w3} sres1 sres2 name r =
  (λ y → fst (sres2 name r) (fst (sres1 name r) y)) ,
  (λ y → snd (sres1 name r) (snd (sres2 name r) y))
--}


upto𝕎getT : (name : Name) (w1 w2 : 𝕎·) (r : ren) → Set
upto𝕎getT name w1 w2 r =
  (n1 n2 : Name) (k : ℕ)
  → ¬ n1 ≡ name
  → ¬ n2 ≡ name
  → names∈ren n1 n2 r
  → getT k n1 w1 ≡ getT k n2 w2


no-repeats : List Name → Set
no-repeats [] = ⊤
no-repeats (n ∷ l) = ¬ n ∈ l × no-repeats l


record wfRen (w1 w2 : 𝕎·) (r : ren) : Set where
  constructor mkWfRen
  field
    wfRenₗ : (n : Name) → n ∈ renₗ r → n ∈ dom𝕎· w1
    wfRenᵣ : (n : Name) → n ∈ renᵣ r → n ∈ dom𝕎· w2
    wfRenNRₗ : no-repeats (renₗ r)
    wfRenNRᵣ : no-repeats (renᵣ r)


-- We know that r is in dom𝕎 w1/dom𝕎 w2 and has no repeats

-- Should be upto a 'ren'
record upto𝕎 (name : Name) (w1 w2 : 𝕎·) (r : ren) : Set(1ℓ Level.⊔ L) where
  constructor mkUpto𝕎
  field
--    upwDom   : dom𝕎· w1 ≡ dom𝕎· w2
--    upwNames : names𝕎· w1 ≡ names𝕎· w2
--    upwRes   : sameRes w1 w2
--    upwWf    : wfRen w1 w2 r
    upwGet   : upto𝕎getT name w1 w2 r



{--
upto𝕎-sym : (name : Name) (w1 w2 : 𝕎·) (r : ren) → upto𝕎 name w1 w2 r → upto𝕎 name w2 w1 (sym-ren r)
upto𝕎-sym name w1 w2 r (mkUpto𝕎 {--eqd eqn sres--} u) =
  mkUpto𝕎
--    (sym eqd)
--    (sym eqn)
--    (sameRes-sym sres)
    (λ n1 n2 k d1 d2 i → sym (u n2 n1 k d2 d1 (names∈ren-sym→ i)))
--}


{--
upto𝕎-trans : (name : Name) (w1 w2 w3 : 𝕎·) (r : ren) → upto𝕎 name w1 w2 r → upto𝕎 name w2 w3 r → upto𝕎 name w1 w3 r
upto𝕎-trans name w1 w2 w3 r (mkUpto𝕎 {--eqd1 eqn1 sres1--} u1) (mkUpto𝕎 {--eqd2 eqn2 sres2--} u2) =
  mkUpto𝕎
--    (trans eqd1 eqd2)
--    (trans eqn1 eqn2)
--    (sameRes-trans sres1 sres2)
    (λ n1 n2 k d1 d2 i → trans (u1 n1 n2 k d1 d2 i) (u2 n2 n2 k d2 d2 (names∈ren-refl n2 r))) {--trans (u1 n1 k d) (u2 n k d)--}
--}


{--
sameRes-chooseT : (cc : ContConds) (name : Name) (w : 𝕎·) (t : Term)
                  → sameRes (chooseT name w t) w
sameRes-chooseT cc name w t n r =
  (λ x → ContConds.ccCchoose→ cc n name w t r x) ,
  (λ x → →compatible-chooseT n name w t r x)
--}


updRel2-NUMₗ→ : {name : Name} {f g : Term} {r : ren} {n : ℕ} {a : Term}
               → updRel2 name f g r (NUM n) a
               → a ≡ NUM n
updRel2-NUMₗ→ {name} {f} {g} {r} {n} {.(NUM n)} (updRel2-NUM .n) = refl



steps-decomp-isHighestℕ2 : {w w1 w2 : 𝕎·} {a b v : Term} {n m : ℕ} (i : ℕ) (name : Name)
              → isValue v
              → (comp1 : steps m (a , w) ≡ (b , w1))
              → (comp2 : steps n (a , w) ≡ (v , w2))
              → Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
                  (isHighestℕ {n} {w} {w2} {a} {v} i name comp2
                   → isHighestℕ {k} {w1} {w2} {b} {v} i name comp)
                  × (∈names𝕎 {n} {w} {w2} {a} {v} name comp2
                     → ∈names𝕎 {k} {w1} {w2} {b} {v} name comp)))
steps-decomp-isHighestℕ2 {w} {w1} {w2} {a} {b} {v} {n} {0} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = n , ≤-refl , comp2 , (λ x → x) , (λ x → x)
steps-decomp-isHighestℕ2 {w} {w1} {w2} {a} {b} {v} {0} {suc m} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
        | stepVal a w isv
        | stepsVal a w m isv
        | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1)
  = 0 , ≤-refl , refl , (λ (j , e , q) → j , e , <-transˡ ≤-refl q) , (λ (nnw , idom) → nnw , idom)
steps-decomp-isHighestℕ2 {w} {w1} {w2} {a} {b} {v} {suc n} {suc m} i name isv comp1 comp2 with step⊎ a w
... | inj₁ (a' , w' , z) rewrite z =
  fst q , ≤-trans (fst (snd q)) (<⇒≤ (n<1+n n)) , fst (snd (snd q)) ,
  (λ (x1 , x2) → fst (snd (snd (snd q))) x2) ,
  (λ (x1 , x2 , x3) → snd (snd (snd (snd q))) x3)
  where
    q : Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
           (isHighestℕ {n} {w'} {w2} {a'} {v} i name comp2
            → isHighestℕ {k} {w1} {w2} {b} {v} i name comp)
           × (∈names𝕎 {n} {w'} {w2} {a'} {v} name comp2
              → ∈names𝕎 {k} {w1} {w2} {b} {v} name comp)))
    q = steps-decomp-isHighestℕ2 {w'} {w1} {w2} {a'} {b} {v} {n} {m} i name isv comp1 comp2
... | inj₂ z rewrite z
           | pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
           | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) =
  0 , _≤_.z≤n , refl , (λ x → x) , (λ x → x)



abstract

  updRel2-refl : {name : Name} {f g : Term} {r : ren} {a : Term}
                 → ¬names a ≡ true
                 → updRel2 name f g r a a
  updRel2-refl {name} {f} {g} {r} {VAR x} nn = updRel2-VAR _
  updRel2-refl {name} {f} {g} {r} {NAT} nn = updRel2-NAT
  updRel2-refl {name} {f} {g} {r} {QNAT} nn = updRel2-QNAT
  updRel2-refl {name} {f} {g} {r} {TNAT} nn = updRel2-TNAT
  updRel2-refl {name} {f} {g} {r} {LT a a₁} nn = updRel2-LT _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {QLT a a₁} nn = updRel2-QLT _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {NUM x} nn = updRel2-NUM _
  updRel2-refl {name} {f} {g} {r} {IFLT a a₁ a₂ a₃} nn = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updRel2-refl {name} {f} {g} {r} {IFEQ a a₁ a₂ a₃} nn = updRel2-IFEQ _ _ _ _ _ _ _ _ (updRel2-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updRel2-refl {name} {f} {g} {r} {SUC a} nn = updRel2-SUC _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {PI a a₁} nn = updRel2-PI _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {LAMBDA a} nn = updRel2-LAMBDA _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {APPLY a a₁} nn = updRel2-APPLY _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {MSEQ s} nn = updRel2-MSEQ _
  updRel2-refl {name} {f} {g} {r} {MAPP s a} nn = updRel2-MAPP _ _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {FIX a} nn = updRel2-FIX _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {LET a a₁} nn = updRel2-LET _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {SUM a a₁} nn = updRel2-SUM _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {PAIR a a₁} nn = updRel2-PAIR _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {SPREAD a a₁} nn = updRel2-SPREAD _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {WT a a₁} nn = updRel2-WT _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {SUP a a₁} nn = updRel2-SUP _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {WREC a a₁} nn = updRel2-WREC _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {MT a a₁} nn = updRel2-MT _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {SET a a₁} nn = updRel2-SET _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {ISECT a a₁} nn = updRel2-ISECT _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {TUNION a a₁} nn = updRel2-TUNION _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {UNION a a₁} nn = updRel2-UNION _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {QTUNION a a₁} nn = updRel2-QTUNION _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {INL a} nn = updRel2-INL _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {INR a} nn = updRel2-INR _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {DECIDE a a₁ a₂} nn = updRel2-DECIDE _ _ _ _ _ _ (updRel2-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel2-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel2-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updRel2-refl {name} {f} {g} {r} {EQ a a₁ a₂} nn = updRel2-EQ _ _ _ _ _ _ (updRel2-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel2-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel2-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updRel2-refl {name} {f} {g} {r} {EQB a a₁ a₂ a₃} nn = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel2-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updRel2-refl {name} {f} {g} {r} {AX} nn = updRel2-AX
  updRel2-refl {name} {f} {g} {r} {FREE} nn = updRel2-FREE
  updRel2-refl {name} {f} {g} {r} {CHOOSE a a₁} nn = updRel2-CHOOSE _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {TSQUASH a} nn = updRel2-TSQUASH _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {TTRUNC a} nn = updRel2-TTRUNC _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {TCONST a} nn = updRel2-TCONST _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {SUBSING a} nn = updRel2-SUBSING _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {PURE} nn = updRel2-PURE
  updRel2-refl {name} {f} {g} {r} {NOSEQ} nn = updRel2-NOSEQ
  updRel2-refl {name} {f} {g} {r} {TERM a} nn = updRel2-TERM _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {ENC a} nn = updRel2-ENC _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {DUM a} nn = updRel2-DUM _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {FFDEFS a a₁} nn = updRel2-FFDEFS _ _ _ _ (updRel2-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel2-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel2-refl {name} {f} {g} {r} {UNIV x} nn = updRel2-UNIV x
  updRel2-refl {name} {f} {g} {r} {LIFT a} nn = updRel2-LIFT _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {LOWER a} nn = updRel2-LOWER _ _ (updRel2-refl nn)
  updRel2-refl {name} {f} {g} {r} {SHRINK a} nn = updRel2-SHRINK _ _ (updRel2-refl nn)



{--
updRel2-refl : {name : Name} {f g : Term} {r : ren} {a : Term}
               → ¬ name ∈ names a
               → updRel2 name f g r a a
updRel2-refl {name} {f} {g} {r} {VAR x} nn = updRel2-VAR _
updRel2-refl {name} {f} {g} {r} {NAT} nn = updRel2-NAT
updRel2-refl {name} {f} {g} {r} {QNAT} nn = updRel2-QNAT
updRel2-refl {name} {f} {g} {r} {TNAT} nn = updRel2-TNAT
updRel2-refl {name} {f} {g} {r} {LT a a₁} nn = updRel2-LT _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {QLT a a₁} nn = updRel2-QLT _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {NUM x} nn = updRel2-NUM _
updRel2-refl {name} {f} {g} {r} {IFLT a a₁ a₂ a₃} nn = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++4→¬∈2 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn)) (updRel2-refl {name} {f} {g} {r} {a₂} (¬∈++4→¬∈3 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn)) (updRel2-refl {name} {f} {g} {r} {a₃} (¬∈++4→¬∈4 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn))
updRel2-refl {name} {f} {g} {r} {SUC a} nn = updRel2-SUC _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {PI a a₁} nn = updRel2-PI _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {LAMBDA a} nn = updRel2-LAMBDA _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {APPLY a a₁} nn = updRel2-APPLY _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {FIX a} nn = updRel2-FIX _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {LET a a₁} nn = updRel2-LET _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {SUM a a₁} nn = updRel2-SUM _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {PAIR a a₁} nn = updRel2-PAIR _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {SPREAD a a₁} nn = updRel2-SPREAD _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {SET a a₁} nn = updRel2-SET _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {TUNION a a₁} nn = updRel2-TUNION _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {ISECT a a₁} nn = updRel2-ISECT _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {UNION a a₁} nn = updRel2-UNION _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {QTUNION a a₁} nn = updRel2-QTUNION _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {INL a} nn = updRel2-INL _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {INR a} nn = updRel2-INR _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {DECIDE a a₁ a₂} nn = updRel2-DECIDE _ _ _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++3→¬∈2 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {r} {a₂} (¬∈++3→¬∈3 {_} {_} {names a} {names a₁} {names a₂} nn))
updRel2-refl {name} {f} {g} {r} {EQ a a₁ a₂} nn = updRel2-EQ _ _ _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++3→¬∈2 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {r} {a₂} (¬∈++3→¬∈3 {_} {_} {names a} {names a₁} {names a₂} nn))
updRel2-refl {name} {f} {g} {r} {AX} nn = updRel2-AX
updRel2-refl {name} {f} {g} {r} {FREE} nn = updRel2-FREE
updRel2-refl {name} {f} {g} {r} {CS x} nn = updRel2-CS x x (λ z → nn (here (sym z))) (λ z → nn (here (sym z))) {!!} {--(names∈ren-refl x r)--} -- updRel2-CS _ λ z → nn (here (sym z))
updRel2-refl {name} {f} {g} {r} {NAME x} nn = updRel2-NAME x x (λ z → nn (here (sym z))) (λ z → nn (here (sym z))) {!!} {--(names∈ren-refl x r)--} -- updRel2-NAME _ λ z → nn (here (sym z))
updRel2-refl {name} {f} {g} {r} {FRESH a} nn = updRel2-FRESH _ _ (updRel2-refl {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {a} (λ z → nn (suc→∈lowerNames {name} {names a} z))) -- updRel2-FRESH _ _ (updRel2-refl {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {a} λ z → nn (suc→∈lowerNames {name} {names a} z))
updRel2-refl {name} {f} {g} {r} {CHOOSE a a₁} nn = updRel2-CHOOSE _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {TSQUASH a} nn = updRel2-TSQUASH _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {TTRUNC a} nn = updRel2-TTRUNC _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {TCONST a} nn = updRel2-TCONST _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {SUBSING a} nn = updRel2-SUBSING _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {DUM a} nn = updRel2-DUM _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {FFDEFS a a₁} nn = updRel2-FFDEFS _ _ _ _ (updRel2-refl {name} {f} {g} {r} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {r} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {r} {PURE} nn = updRel2-PURE
updRel2-refl {name} {f} {g} {r} {TERM a} nn = updRel2-TERM _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {UNIV x} nn = updRel2-UNIV _
updRel2-refl {name} {f} {g} {r} {LIFT a} nn = updRel2-LIFT _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {LOWER a} nn = updRel2-LOWER _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
updRel2-refl {name} {f} {g} {r} {SHRINK a} nn = updRel2-SHRINK _ _ (updRel2-refl {name} {f} {g} {r} {a} nn)
--}


updRel2-LAMBDAₗ→ : {name : Name} {f g : Term} {r : ren} {t : Term} {a : Term}
                  → updRel2 name f g r (LAMBDA t) a
                  → Σ Term (λ u → a ≡ LAMBDA u × updRel2 name f g r t u)
                     ⊎ (t ≡ updBody name f × a ≡ force g)
updRel2-LAMBDAₗ→ {name} {f} {g} {r} {t} {.(LAMBDA a₂)} (updRel2-LAMBDA .t a₂ u) = inj₁ (a₂ , refl , u)
updRel2-LAMBDAₗ→ {name} {f} {g} {r} {.(updBody name f)} {.(force g)} updRel2-upd = inj₂ (refl , refl)



updRel2-PAIRₗ→ : {name : Name} {f g : Term} {r : ren} {t₁ t₂ : Term} {a : Term}
                → updRel2 name f g r (PAIR t₁ t₂) a
                → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ PAIR u₁ u₂ × updRel2 name f g r t₁ u₁ × updRel2 name f g r t₂ u₂))
updRel2-PAIRₗ→ {name} {f} {g} {r} {t₁} {t₂} {.(PAIR a₁ a₂)} (updRel2-PAIR .t₁ a₁ .t₂ a₂ u1 u2) = a₁ , a₂ , refl , u1 , u2



updRel2-SUPₗ→ : {name : Name} {f g : Term} {r : ren} {t₁ t₂ : Term} {a : Term}
                → updRel2 name f g r (SUP t₁ t₂) a
                → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ SUP u₁ u₂ × updRel2 name f g r t₁ u₁ × updRel2 name f g r t₂ u₂))
updRel2-SUPₗ→ {name} {f} {g} {r} {t₁} {t₂} {.(SUP a₁ a₂)} (updRel2-SUP .t₁ a₁ .t₂ a₂ u1 u2) = a₁ , a₂ , refl , u1 , u2



updRel2-INLₗ→ : {name : Name} {f g : Term} {r : ren} {t : Term} {a : Term}
                → updRel2 name f g r (INL t) a
                → Σ Term (λ u → a ≡ INL u × updRel2 name f g r t u)
updRel2-INLₗ→ {name} {f} {g} {r} {t} {.(INL x)} (updRel2-INL .t x u) = x , refl , u



updRel2-INRₗ→ : {name : Name} {f g : Term} {r : ren} {t : Term} {a : Term}
                → updRel2 name f g r (INR t) a
                → Σ Term (λ u → a ≡ INR u × updRel2 name f g r t u)
updRel2-INRₗ→ {name} {f} {g} {r} {t} {.(INR x)} (updRel2-INR .t x u) = x , refl , u




→∈names𝕎-val : {k : ℕ} {name : Name} {a v : Term} {w1 w2 : 𝕎·}
                 → (comp : steps k (a , w1) ≡ (v , w2))
                 → ¬ name ∈ names𝕎· w1
                 → name ∈ dom𝕎· w1
                 → isValue a
                 → ∈names𝕎 {k} {w1} {w2} {a} {v} name comp
→∈names𝕎-val {0} {name} {a} {v} {w1} {w2} comp nnw idom isv
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = nnw , idom
→∈names𝕎-val {suc k} {name} {a} {v} {w1} {w2} comp nnw idom isv with step⊎ a w1
... | inj₁ (a' , w1' , z)
  rewrite z | stepVal a w1 isv | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  nnw , idom , →∈names𝕎-val {k} {name} {a} {v} {w1} {w2} comp nnw idom isv
... | inj₂ z rewrite z = nnw , idom



∈names𝕎-LET→ : {k1 k2 : ℕ} {name : Name} {a b u v : Term} {w1 w2 w3 : 𝕎·}
                 → (comp1 : steps k1 (a , w1) ≡ (u , w2))
                 → (comp2 : steps k2 (LET a b , w1) ≡ (v , w3))
                 → isValue v
                 → ∈names𝕎 {k2} {w1} {w3} {LET a b} {v} name comp2
                 → ∈names𝕎 {k1} {w1} {w2} {a} {u} name comp1
∈names𝕎-LET→ {0} {k2} {name} {a} {b} {u} {v} {w1} {w2} {w3} comp1 comp2 isv h
  rewrite sym (pair-inj₁ comp1) | sym (pair-inj₂ comp1) =
  ∈names𝕎→¬∈name𝕎 {k2} {w1} {w3} {LET a b} {v} name comp2 h ,
  ∈names𝕎→∈dom𝕎 {k2} {w1} {w3} {LET a b} {v} name comp2 h
∈names𝕎-LET→ {suc k1} {0} {name} {a} {b} {u} {v} {w1} {w2} {w3} comp1 comp2 isv h
  rewrite sym (pair-inj₁ comp2) | sym (pair-inj₂ comp2) = ⊥-elim isv
∈names𝕎-LET→ {suc k1} {suc k2} {name} {a} {b} {u} {v} {w1} {w2} {w3} comp1 comp2 isv h
  with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z with isValue⊎ a
... |    inj₁ x rewrite stepVal a w1 x | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  fst h , fst (snd h) , →∈names𝕎-val {k1} {name} {a} {u} {w1} {w2} comp1 (fst h) (fst (snd h)) x
... |    inj₂ x rewrite z = fst h , fst (snd h) , ∈names𝕎-LET→ {k1} {k2} {name} {a'} {b} {u} {v} {w1'} {w2} {w3} comp1 comp2 isv (snd (snd h))
∈names𝕎-LET→ {suc k1} {suc k2} {name} {a} {b} {u} {v} {w1} {w2} {w3} comp1 comp2 isv h | inj₂ z
  rewrite z | sym (pair-inj₁ comp1) | sym (pair-inj₂ comp1) with isValue⊎ a
... | inj₁ x = fst h , fst (snd h)
... | inj₂ x rewrite z = h


abstract

  updRel2-shiftUp : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                    → updRel2 name f g r a b
                    → updRel2 name f g r (shiftUp n a) (shiftUp n b)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(VAR x)} {.(VAR x)} (updRel2-VAR x) = updRel2-VAR _
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.NAT} {.NAT} updRel2-NAT = updRel2-NAT
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.QNAT} {.QNAT} updRel2-QNAT = updRel2-QNAT
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.TNAT} {.TNAT} updRel2-TNAT = updRel2-TNAT
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(NUM x)} {.(NUM x)} (updRel2-NUM x) = updRel2-NUM _
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁) (updRel2-shiftUp n cf cg u₂) (updRel2-shiftUp n cf cg u₃)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (updRel2-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFEQ _ _ _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁) (updRel2-shiftUp n cf cg u₂) (updRel2-shiftUp n cf cg u₃)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-shiftUp (suc n) cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(MSEQ s)} {.(MSEQ s)} (updRel2-MSEQ s) = updRel2-MSEQ _
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(MAPP s a₁)} {.(MAPP s a₂)} (updRel2-MAPP s a₁ a₂ u) = updRel2-MAPP _ _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc (suc n)) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(WT a₁ b₁)} {.(WT a₂ b₂)} (updRel2-WT a₁ a₂ b₁ b₂ u u₁) = updRel2-WT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updRel2-SUP a₁ a₂ b₁ b₂ u u₁) = updRel2-SUP _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (updRel2-WREC a₁ a₂ b₁ b₂ u u₁) = updRel2-WREC _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc (suc (suc n))) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(MT a₁ b₁)} {.(MT a₂ b₂)} (updRel2-MT a₁ a₂ b₁ b₂ u u₁) = updRel2-MT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(INL a₁)} {.(INL a₂)} (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(INR a₁)} {.(INR a₂)} (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁) (updRel2-shiftUp (suc n) cf cg u₂)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁) (updRel2-shiftUp n cf cg u₂)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updRel2-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁) (updRel2-shiftUp n cf cg u₂) (updRel2-shiftUp n cf cg u₃)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.AX} {.AX} updRel2-AX = updRel2-AX
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.FREE} {.FREE} updRel2-FREE = updRel2-FREE
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(CS name1)} {.(CS name2)} (updRel2-CS name1 name2 d1 d2 i) = updRel2-CS name1 name2 d1 d2 i
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(NAME name1)} {.(NAME name2)} (updRel2-NAME name1 name2 d1 d2 i) = updRel2-NAME name1 name2 d1 d2 i
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(FRESH a₁)} {.(FRESH a₂)} (updRel2-FRESH a₁ a₂ r₁) = updRel2-FRESH _ _ (updRel2-shiftUp n (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) r₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(LOAD a)} {.(LOAD a)} (updRel2-LOAD a) = updRel2-LOAD _ ---(updRel2-shiftUp n cf cg r₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(PURE)} {.(PURE)} (updRel2-PURE) = updRel2-PURE
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(NOSEQ)} {.(NOSEQ)} (updRel2-NOSEQ) = updRel2-NOSEQ
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(TERM a₁)} {.(TERM a₂)} (updRel2-TERM a₁ a₂ u) = updRel2-TERM _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(ENC a)} {.(ENC a)} (updRel2-ENC a u) = updRel2-ENC _ u
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(UNIV x)} {.(UNIV x)} (updRel2-UNIV x) = updRel2-UNIV x
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-shiftUp n cf cg u)
  updRel2-shiftUp n {name} {f} {g} {r} cf cg {.(upd name f)} {.(force g)} updRel2-upd
    rewrite #shiftUp (suc (suc n)) (ct g cg)
            | #shiftUp (suc (suc (suc n))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updRel2-upd



abstract

  updRel2-shiftDown : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                      → updRel2 name f g r a b
                      → updRel2 name f g r (shiftDown n a) (shiftDown n b)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(VAR x)} {.(VAR x)} (updRel2-VAR x) = updRel2-VAR _
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.NAT} {.NAT} updRel2-NAT = updRel2-NAT
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.QNAT} {.QNAT} updRel2-QNAT = updRel2-QNAT
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.TNAT} {.TNAT} updRel2-TNAT = updRel2-TNAT
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(NUM x)} {.(NUM x)} (updRel2-NUM x) = updRel2-NUM _
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁) (updRel2-shiftDown n cf cg u₂) (updRel2-shiftDown n cf cg u₃)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (updRel2-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFEQ _ _ _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁) (updRel2-shiftDown n cf cg u₂) (updRel2-shiftDown n cf cg u₃)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-shiftDown (suc n) cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(MSEQ s)} {.(MSEQ s)} (updRel2-MSEQ s) = updRel2-MSEQ _
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(MAPP s a₁)} {.(MAPP s a₂)} (updRel2-MAPP s a₁ a₂ u) = updRel2-MAPP _ _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc (suc n)) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(WT a₁ b₁)} {.(WT a₂ b₂)} (updRel2-WT a₁ a₂ b₁ b₂ u u₁) = updRel2-WT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updRel2-SUP a₁ a₂ b₁ b₂ u u₁) = updRel2-SUP _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (updRel2-WREC a₁ a₂ b₁ b₂ u u₁) = updRel2-WREC _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc (suc (suc n))) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(MT a₁ b₁)} {.(MT a₂ b₂)} (updRel2-MT a₁ a₂ b₁ b₂ u u₁) = updRel2-MT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(INL a₁)} {.(INL a₂)} (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(INR a₁)} {.(INR a₂)} (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁) (updRel2-shiftDown (suc n) cf cg u₂)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁) (updRel2-shiftDown n cf cg u₂)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updRel2-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁) (updRel2-shiftDown n cf cg u₂) (updRel2-shiftDown n cf cg u₃)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.AX} {.AX} updRel2-AX = updRel2-AX
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.FREE} {.FREE} updRel2-FREE = updRel2-FREE
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(CS name1)} {.(CS name2)} (updRel2-CS name1 name2 d1 d2 x) = updRel2-CS name1 name2 d1 d2 x
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(NAME name1)} {.(NAME name2)} (updRel2-NAME name1 name2 d1 d2 x) = updRel2-NAME name1 name2 d1 d2 x
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(FRESH a₁)} {.(FRESH a₂)} (updRel2-FRESH a₁ a₂ r₁) = updRel2-FRESH _ _ (updRel2-shiftDown n (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) r₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(LOAD a)} {.(LOAD a)} (updRel2-LOAD a) = updRel2-LOAD _ -- (updRel2-shiftDown n cf cg r₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(PURE)} {.(PURE)} (updRel2-PURE) = updRel2-PURE
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(NOSEQ)} {.(NOSEQ)} (updRel2-NOSEQ) = updRel2-NOSEQ
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(TERM a₁)} {.(TERM a₂)} (updRel2-TERM a₁ a₂ u) = updRel2-TERM _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(ENC a)} {.(ENC a)} (updRel2-ENC a u) = updRel2-ENC _ u
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(UNIV x)} {.(UNIV x)} (updRel2-UNIV x) = updRel2-UNIV _
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-shiftDown n cf cg u)
  updRel2-shiftDown n {name} {f} {g} {r} cf cg {.(upd name f)} {.(force g)} updRel2-upd
    rewrite #shiftDown (suc (suc n)) (ct g cg)
            | #shiftDown (suc (suc (suc n))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updRel2-upd


sucIf≤-ren : (n : Name) (r : ren) → ren
sucIf≤-ren n [] = []
sucIf≤-ren n ((a , b) ∷ r) = (sucIf≤ n a , sucIf≤ n b) ∷ sucIf≤-ren n r


→∈ren-sucIf≤-ren : (n name1 name2 : Name) (r : ren)
                    → (name1 , name2) ∈ r
                    → (sucIf≤ n name1 , sucIf≤ n name2) ∈ sucIf≤-ren n r
→∈ren-sucIf≤-ren n name1 name2 (x ∷ xs) (here px) rewrite sym px = here refl
→∈ren-sucIf≤-ren n name1 name2 (x ∷ xs) (there i) = there (→∈ren-sucIf≤-ren n name1 name2 xs i)



∈renₗ-sucIf≤-ren→ : {name : Name} {r : ren} (n : Name)
                     → sucIf≤ n name ∈ renₗ (sucIf≤-ren n r)
                     → name ∈ renₗ r
∈renₗ-sucIf≤-ren→ {name} {[]} n ()
∈renₗ-sucIf≤-ren→ {name} {(a , b) ∷ r} n (here px) rewrite sym (sucIf≤-inj {n} {name} {a} px) = here refl
∈renₗ-sucIf≤-ren→ {name} {(a , b) ∷ r} n (there i) = there (∈renₗ-sucIf≤-ren→ {name} {r} n i)



∈renᵣ-sucIf≤-ren→ : {name : Name} {r : ren} (n : Name)
                     → sucIf≤ n name ∈ renᵣ (sucIf≤-ren n r)
                     → name ∈ renᵣ r
∈renᵣ-sucIf≤-ren→ {name} {[]} n ()
∈renᵣ-sucIf≤-ren→ {name} {(a , b) ∷ r} n (here px) rewrite sym (sucIf≤-inj {n} {name} {b} px) = here refl
∈renᵣ-sucIf≤-ren→ {name} {(a , b) ∷ r} n (there i) = there (∈renᵣ-sucIf≤-ren→ {name} {r} n i)



→¬∈renₗ-sucIf≤-ren : {name : Name} {r : ren} (n : Name)
                     → ¬ name ∈ renₗ r
                     → ¬ sucIf≤ n name ∈ renₗ (sucIf≤-ren n r)
→¬∈renₗ-sucIf≤-ren {name} {r} n ni i = ni (∈renₗ-sucIf≤-ren→ {name} {r} n i)



→¬∈renᵣ-sucIf≤-ren : {name : Name} {r : ren} (n : Name)
                     → ¬ name ∈ renᵣ r
                     → ¬ sucIf≤ n name ∈ renᵣ (sucIf≤-ren n r)
→¬∈renᵣ-sucIf≤-ren {name} {r} n ni i = ni (∈renᵣ-sucIf≤-ren→ {name} {r} n i)


→names∈ren-sucIf≤-ren : (n name1 name2 : Name) (r : ren)
                         → names∈ren name1 name2 r
                         → names∈ren (sucIf≤ n name1) (sucIf≤ n name2) (sucIf≤-ren n r)
→names∈ren-sucIf≤-ren n name1 name2 [] i rewrite i = refl
→names∈ren-sucIf≤-ren n name1 name2 ((a , b) ∷ r) (inj₁ (u , v)) rewrite u | v = inj₁ (refl , refl)
→names∈ren-sucIf≤-ren n name1 name2 ((a , b) ∷ r) (inj₂ (u , v , x)) =
  inj₂ ((λ z → u (sucIf≤-inj z)) , (λ z → v (sucIf≤-inj z)) , →names∈ren-sucIf≤-ren n name1 name2 r x)
{-- r (inj₁ (e , i₁ , i₂)) rewrite e = inj₁ (refl , →¬∈renₗ-sucIf≤-ren n i₁ , →¬∈renᵣ-sucIf≤-ren n i₂) --inj₁ refl
→names∈ren-sucIf≤-ren n name1 name2 r (inj₂ i) = inj₂ (→∈ren-sucIf≤-ren n name1 name2 r i)
--}


sucIf≤-ren-suc-sren : (n : Name) (r : ren)
                      → sucIf≤-ren (suc n) (sren r)
                         ≡ sren (sucIf≤-ren n r)
sucIf≤-ren-suc-sren n [] = refl
sucIf≤-ren-suc-sren n ((a , b) ∷ r)
  rewrite suc-sucIf≤ n a | suc-sucIf≤ n b | sucIf≤-ren-suc-sren n r = refl



abstract

  updRel2-shiftNameUp : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                        → updRel2 name f g r a b
                        → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) (shiftNameUp n a) (shiftNameUp n b)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(VAR x)} {.(VAR x)} (updRel2-VAR x) = updRel2-VAR _
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.NAT} {.NAT} updRel2-NAT = updRel2-NAT
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.QNAT} {.QNAT} updRel2-QNAT = updRel2-QNAT
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.TNAT} {.TNAT} updRel2-TNAT = updRel2-TNAT
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(NUM x)} {.(NUM x)} (updRel2-NUM x) = updRel2-NUM _
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂) (updRel2-shiftNameUp n cf cg u₃)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (updRel2-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFEQ _ _ _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂) (updRel2-shiftNameUp n cf cg u₃)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(MSEQ s)} {.(MSEQ s)} (updRel2-MSEQ s) = updRel2-MSEQ _
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(MAPP s a₁)} {.(MAPP s a₂)} (updRel2-MAPP s a₁ a₂ u) = updRel2-MAPP _ _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(WT a₁ b₁)} {.(WT a₂ b₂)} (updRel2-WT a₁ a₂ b₁ b₂ u u₁) = updRel2-WT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updRel2-SUP a₁ a₂ b₁ b₂ u u₁) = updRel2-SUP _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (updRel2-WREC a₁ a₂ b₁ b₂ u u₁) = updRel2-WREC _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(MT a₁ b₁)} {.(MT a₂ b₂)} (updRel2-MT a₁ a₂ b₁ b₂ u u₁) = updRel2-MT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(INL a₁)} {.(INL a₂)} (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(INR a₁)} {.(INR a₂)} (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updRel2-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂) (updRel2-shiftNameUp n cf cg u₃)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.AX} {.AX} updRel2-AX = updRel2-AX
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.FREE} {.FREE} updRel2-FREE = updRel2-FREE
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(CS name1)} {.(CS name2)} (updRel2-CS name1 name2 d1 d2 i) = updRel2-CS (sucIf≤ n name1) (sucIf≤ n name2) (λ z → d1 (sucIf≤-inj z)) (λ z → d2 (sucIf≤-inj z)) (→names∈ren-sucIf≤-ren n name1 name2 r i)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(NAME name1)} {.(NAME name2)} (updRel2-NAME name1 name2 d1 d2 i) = updRel2-NAME (sucIf≤ n name1) (sucIf≤ n name2) (λ z → d1 (sucIf≤-inj z)) (λ z → d2 (sucIf≤-inj z)) (→names∈ren-sucIf≤-ren n name1 name2 r i)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(FRESH a₁)} {.(FRESH a₂)} (updRel2-FRESH a₁ a₂ r₁) =
    updRel2-FRESH (shiftNameUp (suc n) a₁) (shiftNameUp (suc n) a₂) c1
    where
      c3 : updRel2 (sucIf≤ (suc n) (suc name))
                   (shiftNameUp (suc n) (shiftNameUp 0 f))
                   (shiftNameUp (suc n) (shiftNameUp 0 g))
                   (sucIf≤-ren (suc n) (sren r))
                   (shiftNameUp (suc n) a₁)
                   (shiftNameUp (suc n) a₂)
      c3 = updRel2-shiftNameUp (suc n) {suc name} (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) r₁

      c2 : updRel2 (suc (sucIf≤ n name))
                   (shiftNameUp (suc n) (shiftNameUp 0 f))
                   (shiftNameUp (suc n) (shiftNameUp 0 g))
                   (sren (sucIf≤-ren n r))
                   (shiftNameUp (suc n) a₁)
                   (shiftNameUp (suc n) a₂)
      c2 rewrite suc-sucIf≤ n name | sym (sucIf≤-ren-suc-sren n r) = c3

      c1 : updRel2 (suc (sucIf≤ n name))
                   (shiftNameUp 0 (shiftNameUp n f))
                   (shiftNameUp 0 (shiftNameUp n g))
                   (sren (sucIf≤-ren n r))
                   (shiftNameUp (suc n) a₁)
                   (shiftNameUp (suc n) a₂)
      c1 rewrite shiftNameUp-shiftNameUp {0} {n} {f} _≤_.z≤n | shiftNameUp-shiftNameUp {0} {n} {g} _≤_.z≤n = c2
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(LOAD a)} {.(LOAD a)} (updRel2-LOAD a) = updRel2-LOAD _ --(updRel2-shiftNameUp n cf cg u) --(updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(PURE)} {.(PURE)} (updRel2-PURE) = updRel2-PURE
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(NOSEQ)} {.(NOSEQ)} (updRel2-NOSEQ) = updRel2-NOSEQ
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(TERM a₁)} {.(TERM a₂)} (updRel2-TERM a₁ a₂ u) = updRel2-TERM _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(ENC a)} {.(ENC a)} (updRel2-ENC a u) = updRel2-ENC _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(UNIV x)} {.(UNIV x)} (updRel2-UNIV x) = updRel2-UNIV x
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-shiftNameUp n cf cg u)
  updRel2-shiftNameUp n {name} {f} {g} {r} cf cg {.(upd name f)} {.(force g)} updRel2-upd = c2
    where
      c1 : updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) (upd (sucIf≤ n name) (shiftNameUp n f)) (force (shiftNameUp n g))
      c1 = updRel2-upd

      c2 : updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r)
                   (LAMBDA (LET (VAR 0)
                                (LET (IFLT (APPLY (CS (sucIf≤ n name)) (NUM 0)) (VAR 0)
                                           (CHOOSE (NAME (sucIf≤ n name)) (VAR 0)) AX)
                                     (APPLY (shiftNameUp n (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
                   (LAMBDA (LET (VAR 0) (APPLY (shiftNameUp n g) (VAR 0))))
      c2 rewrite sym (shiftUp-shiftNameUp 0 n f) = c1



sren≡sucIf≤0-ren : (r : ren) → sren r ≡ sucIf≤-ren 0 r
sren≡sucIf≤0-ren [] = refl
sren≡sucIf≤0-ren ((a , b) ∷ r)
  rewrite suc≡sucIf≤0 a | suc≡sucIf≤0 b | sren≡sucIf≤0-ren r = refl



updRel2-shiftNameUp0 : {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                   → updRel2 name f g r a b
                   → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) (sren r) (shiftNameUp 0 a) (shiftNameUp 0 b)
updRel2-shiftNameUp0 {name} {f} {g} {r} cf cg {a} {b} u
  rewrite suc≡sucIf≤0 name | sren≡sucIf≤0-ren r =
  updRel2-shiftNameUp 0 {name} cf cg u



abstract

  updRel2-subv : (v : Var) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a₁ a₂ b₁ b₂ : Term}
                 → updRel2 name f g r a₁ a₂
                 → updRel2 name f g r b₁ b₂
                 → updRel2 name f g r (subv v b₁ a₁) (subv v b₂ a₂)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(VAR x)} {.(VAR x)} {b₁} {b₂} (updRel2-VAR x) ub with x ≟ v
  ... | yes p = ub
  ... | no p = updRel2-VAR x
  updRel2-subv v {name} {f} {g} {r} cf cg {.NAT} {.NAT} {b₁} {b₂} updRel2-NAT ub = updRel2-NAT
  updRel2-subv v {name} {f} {g} {r} cf cg {.QNAT} {.QNAT} {b₁} {b₂} updRel2-QNAT ub = updRel2-QNAT
  updRel2-subv v {name} {f} {g} {r} cf cg {.TNAT} {.TNAT} {b₁} {b₂} updRel2-TNAT ub = updRel2-TNAT
  updRel2-subv v {name} {f} {g} {r} cf cg {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (updRel2-LT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-LT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (updRel2-QLT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-QLT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(NUM x)} {.(NUM x)} {b₁} {b₂} (updRel2-NUM x) ub = updRel2-NUM x
  updRel2-subv v {name} {f} {g} {r} cf cg {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₂)} {b₁} {b₂} (updRel2-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub) (updRel2-subv v cf cg ua₂ ub) (updRel2-subv v cf cg ua₃ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(IFEQ a₁ b₃ c₁ d₁)} {.(IFEQ a₂ b₄ c₂ d₂)} {b₁} {b₂} (updRel2-IFEQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updRel2-IFEQ _ _ _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub) (updRel2-subv v cf cg ua₂ ub) (updRel2-subv v cf cg ua₃ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SUC a₁)} {.(SUC a₂)} {b₁} {b₂} (updRel2-SUC a₁ a₂ ua) ub = updRel2-SUC _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (updRel2-PI a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-PI _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} {b₁} {b₂} (updRel2-LAMBDA a₁ a₂ ua) ub = updRel2-LAMBDA _ _ (updRel2-subv (suc v) cf cg ua (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (updRel2-APPLY a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-APPLY _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(MSEQ s)} {.(MSEQ s)} {b₁} {b₂} (updRel2-MSEQ s) ub = updRel2-MSEQ _
  updRel2-subv v {name} {f} {g} {r} cf cg {.(MAPP s a₁)} {.(MAPP s a₂)} {b₁} {b₂} (updRel2-MAPP s a₁ a₂ ua) ub = updRel2-MAPP _ _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(FIX a₁)} {.(FIX a₂)} {b₁} {b₂} (updRel2-FIX a₁ a₂ ua) ub = updRel2-FIX _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (updRel2-LET a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-LET _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (updRel2-SUM a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SUM _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (updRel2-PAIR a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-PAIR _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (updRel2-SPREAD a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SPREAD _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc (suc v)) cf cg ua₁ (updRel2-shiftUp 0 cf cg (updRel2-shiftUp 0 cf cg ub)))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(WT a₁ b₃)} {.(WT a₂ b₄)} {b₁} {b₂} (updRel2-WT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-WT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SUP a₁ b₃)} {.(SUP a₂ b₄)} {b₁} {b₂} (updRel2-SUP a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SUP _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(WREC a₁ b₃)} {.(WREC a₂ b₄)} {b₁} {b₂} (updRel2-WREC a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-WREC _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc (suc (suc v))) cf cg ua₁ (updRel2-shiftUp 0 cf cg (updRel2-shiftUp 0 cf cg (updRel2-shiftUp 0 cf cg ub))))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(MT a₁ b₃)} {.(MT a₂ b₄)} {b₁} {b₂} (updRel2-MT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-MT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (updRel2-SET a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SET _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(ISECT a₁ b₃)} {.(ISECT a₂ b₄)} {b₁} {b₂} (updRel2-ISECT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-ISECT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (updRel2-TUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-TUNION _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (updRel2-UNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-UNION _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (updRel2-QTUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-QTUNION _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(INL a₁)} {.(INL a₂)} {b₁} {b₂} (updRel2-INL a₁ a₂ ua) ub = updRel2-INL _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(INR a₁)} {.(INR a₂)} {b₁} {b₂} (updRel2-INR a₁ a₂ ua) ub = updRel2-INR _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (updRel2-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updRel2-DECIDE _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub)) (updRel2-subv (suc v) cf cg ua₂ (updRel2-shiftUp 0 cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (updRel2-EQ a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updRel2-EQ _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub) (updRel2-subv v cf cg ua₂ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(EQB a₁ b₃ c₁ d₁)} {.(EQB a₂ b₄ c₂ d₂)} {b₁} {b₂} (updRel2-EQB a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub) (updRel2-subv v cf cg ua₂ ub) (updRel2-subv v cf cg ua₃ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.AX} {.AX} {b₁} {b₂} updRel2-AX ub = updRel2-AX
  updRel2-subv v {name} {f} {g} {r} cf cg {.FREE} {.FREE} {b₁} {b₂} updRel2-FREE ub = updRel2-FREE
  updRel2-subv v {name} {f} {g} {r} cf cg {.(CS name1)} {.(CS name2)} {b₁} {b₂} (updRel2-CS name1 name2 d1 d2 x) ub = updRel2-CS name1 name2 d1 d2 x
  updRel2-subv v {name} {f} {g} {r} cf cg {.(NAME name1)} {.(NAME name2)} {b₁} {b₂} (updRel2-NAME name1 name2 d1 d2 x) ub = updRel2-NAME name1 name2 d1 d2 x
  updRel2-subv v {name} {f} {g} {r} cf cg {.(FRESH a₁)} {.(FRESH a₂)} {b₁} {b₂} (updRel2-FRESH a₁ a₂ ua) ub = updRel2-FRESH _ _ (updRel2-subv v {suc name} (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) {a₁} {a₂} {shiftNameUp 0 b₁} {shiftNameUp 0 b₂} ua (updRel2-shiftNameUp0 {name} cf cg ub))
  updRel2-subv v {name} {f} {g} {r} cf cg {.(LOAD a)} {.(LOAD a)} {b₁} {b₂} (updRel2-LOAD a) ub = updRel2-LOAD _ --ua -- (updRel2-subv v {name} cf cg {a₁} {a₂} {b₁} {b₂} ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (updRel2-CHOOSE a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-CHOOSE _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} {b₁} {b₂} (updRel2-TSQUASH a₁ a₂ ua) ub = updRel2-TSQUASH _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} {b₁} {b₂} (updRel2-TTRUNC a₁ a₂ ua) ub = updRel2-TTRUNC _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(TCONST a₁)} {.(TCONST a₂)} {b₁} {b₂} (updRel2-TCONST a₁ a₂ ua) ub = updRel2-TCONST _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} {b₁} {b₂} (updRel2-SUBSING a₁ a₂ ua) ub = updRel2-SUBSING _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(PURE)} {.(PURE)} {b₁} {b₂} (updRel2-PURE) ub = updRel2-PURE
  updRel2-subv v {name} {f} {g} {r} cf cg {.(NOSEQ)} {.(NOSEQ)} {b₁} {b₂} (updRel2-NOSEQ) ub = updRel2-NOSEQ
  updRel2-subv v {name} {f} {g} {r} cf cg {.(TERM a₁)} {.(TERM a₂)} {b₁} {b₂} (updRel2-TERM a₁ a₂ ua) ub = updRel2-TERM _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(ENC a)} {.(ENC a)} {b₁} {b₂} (updRel2-ENC a ua) ub = updRel2-ENC _ ua
  updRel2-subv v {name} {f} {g} {r} cf cg {.(DUM a₁)} {.(DUM a₂)} {b₁} {b₂} (updRel2-DUM a₁ a₂ ua) ub = updRel2-DUM _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (updRel2-FFDEFS a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-FFDEFS _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (updRel2-UNIV x) ub = updRel2-UNIV x
  updRel2-subv v {name} {f} {g} {r} cf cg {.(LIFT a₁)} {.(LIFT a₂)} {b₁} {b₂} (updRel2-LIFT a₁ a₂ ua) ub = updRel2-LIFT _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(LOWER a₁)} {.(LOWER a₂)} {b₁} {b₂} (updRel2-LOWER a₁ a₂ ua) ub = updRel2-LOWER _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} {b₁} {b₂} (updRel2-SHRINK a₁ a₂ ua) ub = updRel2-SHRINK _ _ (updRel2-subv v cf cg ua ub)
  updRel2-subv v {name} {f} {g} {r} cf cg {.(upd name f)} {.(force g)} {b₁} {b₂} updRel2-upd ub
    rewrite subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₁))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
            | subv# (suc (suc v)) (shiftUp 0 (shiftUp 0 b₂)) g cg
    = updRel2-upd



updRel2-sub : {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a₁ a₂ b₁ b₂ : Term}
             → updRel2 name f g r a₁ a₂
             → updRel2 name f g r b₁ b₂
             → updRel2 name f g r (sub b₁ a₁) (sub b₂ a₂)
updRel2-sub {name} {f} {g} {r} cf cg {a₁} {a₂} {b₁} {b₂} ua ub =
  updRel2-shiftDown 0 cf cg (updRel2-subv 0 cf cg ua (updRel2-shiftUp 0 cf cg ub))


upto𝕎→upto𝕎getT : {name : Name} {w1 w2 : 𝕎·} {r : ren}
                     → upto𝕎 name w1 w2 r
                     → upto𝕎getT name w1 w2 r
upto𝕎→upto𝕎getT {name} {w1} {w2} {r} upw = upto𝕎.upwGet upw


{--
upto𝕎→≡dom𝕎 : {name : Name} {w1 w2 : 𝕎·}
                 → upto𝕎 name w1 w2
                 → dom𝕎· w1 ≡ dom𝕎· w2
upto𝕎→≡dom𝕎 {name} {w1} {w2} upw = upto𝕎.upwDom upw
--}


{--
upto𝕎→≡names𝕎 : {name : Name} {w1 w2 : 𝕎·}
                 → upto𝕎 name w1 w2
                 → names𝕎· w1 ≡ names𝕎· w2
upto𝕎→≡names𝕎 {name} {w1} {w2} upw = upto𝕎.upwNames upw
--}


{--
getT≡→map-getT≡ : {n : ℕ} {name name' : Name} {w w' : 𝕎·} {r : ren} {t : Term}
                   → ¬ name' ≡ name
                   → upto𝕎 name w w' r
                   → getT n name' w ≡ just t
                   → Data.Maybe.map (λ t → t , w') (getT n name' w') ≡ just (t , w')
getT≡→map-getT≡ {n} {name} {name'} {w} {w'} {r} {t} neq upw gt
  rewrite sym (upto𝕎→upto𝕎getT upw name' n neq) | gt = refl
--}


≡N→≡freshName : {a b : List Name}
                 → a ≡N b
                 → fst (freshName a) ≡ fst (freshName b)
≡N→≡freshName {a} {b} e = ≡N→≡freshNameAux e


→≡++ : {a b c d : List Name} → a ≡ b → c ≡ d → (a ++ c) ≡ (b ++ d)
→≡++ {a} {b} {c} {d} e f rewrite e | f = refl


→≡N++ : {a b c d : List Name} → a ≡N b → c ≡N d → (a ++ c) ≡N (b ++ d)
→≡N++ {a} {b} {c} {d} e f x =
  h1 , h2
  where
    h1 : x ∈ a ++ c → x ∈ b ++ d
    h1 i with ∈-++⁻ a i
    ... | inj₁ p = ∈-++⁺ˡ (fst (e x) p)
    ... | inj₂ p = ∈-++⁺ʳ b (fst (f x) p)

    h2 : x ∈ b ++ d → x ∈ a ++ c
    h2 i with ∈-++⁻ b i
    ... | inj₁ p = ∈-++⁺ˡ (snd (e x) p)
    ... | inj₂ p = ∈-++⁺ʳ a (snd (f x) p)


{--
upto𝕎→≡newChoiceT : {name : Name} {w1 w2 : 𝕎·} (a : Term)
                       → upto𝕎 name w1 w2
                       → newChoiceT w1 a ≡ newChoiceT w2 a
upto𝕎→≡newChoiceT {name} {w1} {w2} a upw =
  ≡N→≡freshName
    {dom𝕎· w1 ++ names𝕎· w1 ++ ↓vars (names a)}
    {dom𝕎· w2 ++ names𝕎· w2 ++ ↓vars (names a)}
    (≡→≡N (→≡++ (upto𝕎.upwDom upw)
                  (→≡++ (upto𝕎.upwNames upw) refl)))
--}


{--
upto𝕎→≡newChoiceT+ : {name : Name} {w1 w2 : 𝕎·} (a : Term)
                       → upto𝕎 name w1 w2
                       → newChoiceT+ w1 a ≡ newChoiceT+ w2 a
upto𝕎→≡newChoiceT+ {name} {w1} {w2} a upw
  rewrite upto𝕎→≡newChoiceT a upw = refl
--}


-- MOVE to computation
fresh-inst : (w : 𝕎·) (a : Term) → Term
fresh-inst w a = shiftNameDown 0 (renn 0 (newChoiceT+ w a) a)


{--
upto𝕎→≡fresh-inst : {name : Name} {w1 w2 : 𝕎·} (a : Term)
                      → upto𝕎 name w1 w2
                      → fresh-inst w1 a ≡ fresh-inst w2 a
upto𝕎→≡fresh-inst {name} {w1} {w2} a upw rewrite upto𝕎→≡newChoiceT+ a upw = refl
--}




≡pres∈ : {a b : List Name} {x : Name}
          → a ≡ b
          → x ∈ a
          → x ∈ b
≡pres∈ {a} {b} {x} e i rewrite e = i


≡pres¬∈ : {a b : List Name} {x : Name}
          → a ≡ b
          → ¬ x ∈ a
          → ¬ x ∈ b
≡pres¬∈ {a} {b} {x} e ni rewrite e = ni



{--
sameRes-startChoice : (cc : ContConds) (n : ℕ) (w1 w2 : 𝕎·)
                      → dom𝕎· w1 ≡ dom𝕎· w2
                      → sameRes w1 w2
                      → sameRes (startChoice· n Res⊤ w1) (startChoice· n Res⊤ w2)
sameRes-startChoice cc n w1 w2 eqd same name r =
  c1 , c2
  where
    c1 : compatible· name (startChoice· n Res⊤ w1) r → compatible· name (startChoice· n Res⊤ w2) r
    c1 compat with n ≟ name
    ... | yes p rewrite p with Name∈⊎ name (dom𝕎· w1)
    ... |    inj₁ i = ContConds.ccC∈start← cc name r Res⊤ w2 (≡pres∈ eqd i) (fst (same name r) (ContConds.ccC∈start→ cc name r Res⊤ w1 i compat))
    ... |    inj₂ ni rewrite sym (ContConds.ccC¬∈start→ cc name r Res⊤ w1 ni compat) = startChoiceCompatible· Res⊤ w2 name (≡pres¬∈ eqd ni)
    c1 compat | no p = ContConds.ccC¬≡start← cc n name r Res⊤ w2 p (fst (same name r) (ContConds.ccC¬≡start→ cc n name r Res⊤ w1 p compat))

    c2 : compatible· name (startChoice· n Res⊤ w2) r → compatible· name (startChoice· n Res⊤ w1) r
    c2 compat with n ≟ name
    ... | yes p rewrite p with Name∈⊎ name (dom𝕎· w2)
    ... |    inj₁ i = ContConds.ccC∈start← cc name r Res⊤ w1 (≡pres∈ (sym eqd) i) (snd (same name r) (ContConds.ccC∈start→ cc name r Res⊤ w2 i compat))
    ... |    inj₂ ni rewrite sym (ContConds.ccC¬∈start→ cc name r Res⊤ w2 ni compat) = startChoiceCompatible· Res⊤ w1 name (≡pres¬∈ (sym eqd) ni)
    c2 compat | no p = ContConds.ccC¬≡start← cc n name r Res⊤ w1 p (snd (same name r) (ContConds.ccC¬≡start→ cc n name r Res⊤ w2 p compat))
--}



{--
→upto𝕎-startChoice : (cc : ContConds) {name : Name} {w1 w2 : 𝕎·} {r : ren} (n : Name)
                       → upto𝕎 name w1 w2 r
                       → upto𝕎 name (startChoice· n Res⊤ w1) (startChoice· n Res⊤ w2) r
→upto𝕎-startChoice cc {name} {w1} {w2} {r} n upw =
  mkUpto𝕎
    -- (ContConds.ccD≡start cc n w1 w2 (upto𝕎.upwDom upw))
    -- (→≡names𝕎-start cc n w1 w2 (upto𝕎.upwNames upw))
    -- (sameRes-startChoice cc n w1 w2 (upto𝕎.upwDom upw) (upto𝕎.upwRes upw))
    λ n1 n2 k d1 d2 i → {!!} --(λ nm k d → upto𝕎→≡getT cc k nm name n w1 w2 d (upto𝕎.upwGet upw nm k d))
--}



{--
→upto𝕎-startNewChoiceT : (cc : ContConds) {name : Name} {w1 w2 : 𝕎·} {r : ren} (a : Term)
                           → upto𝕎 name w1 w2 r
                           → upto𝕎 name (startNewChoiceT Res⊤ w1 a) (startNewChoiceT Res⊤ w2 a) r
→upto𝕎-startNewChoiceT cc {name} {w1} {w2} {r} a upw
  rewrite upto𝕎→≡newChoiceT a upw = →upto𝕎-startChoice cc (newChoiceT w2 a) upw
--}



{--
→upto𝕎getT-chooseT : (cc : ContConds) (name name' : Name) (w1 w1' : 𝕎·) (t : Term)
                 → upto𝕎 name w1 w1'
                 → upto𝕎getT name (chooseT name' w1 t) (chooseT name' w1' t)
→upto𝕎getT-chooseT cc name name' w1 w1' t upw n k dn with n ≟ name'
... | yes p rewrite p = ContConds.ccGget cc name' w1 w1' t k (λ z → upto𝕎.upwGet upw name' z dn) (upto𝕎.upwRes upw) (upto𝕎.upwDom upw) -- we need w1 and w1' to have the same restritions
... | no p = trans (ContConds.ccGcd cc k n name' w1 t p)
                   (trans (upto𝕎.upwGet upw n k dn)
                          (sym (ContConds.ccGcd cc k n name' w1' t p)))
--}


{--
→sameRes-chooseT : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (t : Term)
                    → sameRes w1 w2
                    → sameRes (chooseT name w1 t) (chooseT name w2 t)
→sameRes-chooseT cc name w1 w2 t same =
  sameRes-trans (sameRes-chooseT cc name w1 t)
                (sameRes-trans same (sameRes-sym (sameRes-chooseT cc name w2 t)))
--}


→≡-names𝕎-chooseT : (cc : ContConds) (w1 w2 : 𝕎·) (name : Name) (t : Term)
                       → names𝕎· w1 ≡ names𝕎· w2
                       → names𝕎· (chooseT name w1 t) ≡ names𝕎· (chooseT name w2 t)
→≡-names𝕎-chooseT cc w1 w2 name t eqn
  rewrite ContConds.ccNchoose≡ cc name w1 t
        | ContConds.ccNchoose≡ cc name w2 t = eqn


→≡N-names𝕎-chooseT : (cc : ContConds) (w1 w2 : 𝕎·) (name : Name) (t : Term)
                       → names𝕎· w1 ≡N names𝕎· w2
                       → names𝕎· (chooseT name w1 t) ≡N names𝕎· (chooseT name w2 t)
→≡N-names𝕎-chooseT cc w1 w2 name t eqn n
  rewrite ContConds.ccNchoose≡ cc name w1 t
        | ContConds.ccNchoose≡ cc name w2 t = eqn n



{--
upto𝕎-chooseT : (cc : ContConds) (name name' : Name) (w1 w1' : 𝕎·) (t : Term)
                 → upto𝕎 name w1 w1'
                 → upto𝕎 name (chooseT name' w1 t) (chooseT name' w1' t)
upto𝕎-chooseT cc name name' w1 w1' t upw =
  mkUpto𝕎
    (→dom𝕎-chooseT≡ cc name' w1 w1' t (upto𝕎.upwDom upw))
    (→≡-names𝕎-chooseT cc w1 w1' name' t (upto𝕎.upwNames upw)) -- we need to assume here that w1 and w1' have the same restrictions and change this requirement to be a set equality instead of a list equality
    (→sameRes-chooseT cc name' w1 w1' t (upto𝕎.upwRes upw))
    (→upto𝕎getT-chooseT cc name name' w1 w1' t upw)
--}


{--
updRel2-CSₗ→ : {name : Name} {f g : Term} {r : ren} {n : Name} {a : Term}
               → updRel2 name f g r (CS n) a
               → a ≡ CS n
updRel2-CSₗ→ {name} {f} {g} {r} {n} {.(CS n)} (updRel2-CS .n x) = refl


updRel2-CSₗ→¬≡ : {name : Name} {f g : Term} {r : ren} {n : Name} {a : Term}
               → updRel2 name f g r (CS n) a
               → ¬ n ≡ name
updRel2-CSₗ→¬≡ {name} {f} {g} {r} {n} {.(CS n)} (updRel2-CS .n x) = x



isHighestℕ2-APPLY₁→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {a b v : Term} {w w' : 𝕎·}
                      → (comp : steps k (APPLY a b , w) ≡ (v , w'))
                      → isValue v
                      → isHighestℕ {k} {w} {w'} {APPLY a b} {v} n name comp
                      → ∈names𝕎 {k} {w} {w'} {APPLY a b} {v} name comp
                      → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × ∈names𝕎 {k'} {w} {w''} {a} {u} name comp'
                          × isValue u
                          × k' < k))))
isHighestℕ2-APPLY₁→ {n} {0} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ2-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw with is-LAM a
... | inj₁ (t , p) rewrite p = 0 , LAMBDA t , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... | inj₂ x with is-CS a
... |    inj₁ (name' , q) rewrite q with is-NUM b
... |       inj₁ (j , r) rewrite r with getT j name' w
... |          just t = 0 , CS name' , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... |          nothing = 0 , CS name' , w , refl , h , inw , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ2-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw | inj₂ x | inj₁ (name' , q) | inj₂ r with step⊎ b w
... |          inj₁ (b0 , w0 , z) rewrite z = 0 , CS name' , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... |          inj₂ z rewrite z = 0 , CS name' , w , refl , h , inw , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ2-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw | inj₂ x | inj₂ y with step⊎ a w
... |    inj₁ (a0 , w0 , z) rewrite z =
  suc (fst ind) , concl
  where
    ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a0 , w0) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w0} {w''} {a0} {u} n name comp'
                          × ∈names𝕎 {k'} {w0} {w''} {a0} {u} name comp'
                          × isValue u
                          × k' < k))))
    ind = isHighestℕ2-APPLY₁→ {n} {k} {name} {f} {g} {a0} {b} {v} {w0} {w'} comp isv (snd h) (snd (snd inw))

    concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {suc (fst ind)} {w} {w''} {a} {u} n name comp'
                          × ∈names𝕎 {suc (fst ind)} {w} {w''} {a} {u} name comp'
                          × isValue u
                          × suc (fst ind) < suc k)))
    concl rewrite z =
      fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
      (fst h , fst (snd (snd (snd (snd ind))))) ,
      (fst inw , fst (snd inw) , fst (snd (snd (snd (snd (snd ind)))))) ,
      fst (snd (snd (snd (snd (snd (snd ind)))))) ,
      _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd ind)))))))
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsPresUpdRel2-APPLY₁→ : {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w : 𝕎·}
                           → stepsPresUpdRel2 n name f g (APPLY a b) w
                           → stepsPresUpdRel2 n name f g a w
stepsPresUpdRel2-APPLY₁→ {n} {name} {f} {g} {a} {b} {w} (k , v , w' , comp , isv , ish , inw , ind) =
  fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
  fst (snd (snd (snd (snd (snd (snd hv)))))) , fst (snd (snd (snd (snd hv)))) ,
  fst (snd (snd (snd (snd (snd hv))))) ,
  λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd (snd hv)))))))))
  where
    hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × ∈names𝕎 {k'} {w} {w''} {a} {u} name comp'
                          × isValue u
                          × k' < k))))
    hv = isHighestℕ2-APPLY₁→ {n} {k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv ish inw





→ΣstepsUpdRel2-APPLY₁ : {name : Name} {f g : Term} {a₁ a₂ b₁ b₂ : Term} {w1 w : 𝕎·}
                        → updRel2 name f g r b₁ b₂
                        → ΣstepsUpdRel2 name f g a₁ w1 a₂ w
                        → ΣstepsUpdRel2 name f g (APPLY a₁ b₁) w1 (APPLY a₂ b₂) w
→ΣstepsUpdRel2-APPLY₁ {name} {f} {g} {a₁} {a₂} {b₁} {b₂} {w1} {w} updb (k1 , k2 , y1 , y2 , w3 , w' , comp1 , comp2 , r , upw) =
  fst comp1' , fst comp2' , APPLY y1 b₁ , APPLY y2 b₂ , w3 , w' , snd comp1' , snd comp2' ,
  updRel2-APPLY _ _ _ _ r updb , upw
  where
    comp1' : APPLY a₁ b₁ ⇓ APPLY y1 b₁ from w1 to w3
    comp1' = →steps-APPLY b₁ k1 comp1

    comp2' : APPLY a₂ b₂ ⇓ APPLY y2 b₂ from w to w'
    comp2' = →steps-APPLY b₂ k2 comp2


Σsteps-updRel2-NUM→ : {name : Name} {f g : Term} {r : ren} {m : ℕ} {b : Term} {w1 : 𝕎·} {w2 : 𝕎·}
                      → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w1' → steps k' (b , w1) ≡ (v' , w1') × updRel2 name f g r (NUM m) v' × upto𝕎 name w2 w1' r)))
                      → Σ ℕ (λ k' → Σ 𝕎· (λ w1' → steps k' (b , w1) ≡ (NUM m , w1') × upto𝕎 name w2 w1'))
Σsteps-updRel2-NUM→ {name} {f} {g} {r} {m} {b} {w1} {w2} (k' , .(NUM m) , w1' , comp , updRel2-NUM .m , upw) = k' , w1' , comp , upw
--}


{--
upto𝕎getT-chooseT : (cc : ContConds) (name : Name) (w : 𝕎·) (r : ren) (t : Term)
                     → upto𝕎getT name w (chooseT name w t) r
upto𝕎getT-chooseT cc name w r t n1 n2 k d1 d2 i
  rewrite ContConds.ccGcd cc k n2 name w t d2 =
  {!!} --sym (ContConds.ccGcd cc k nm name w t d)
--}


{--
upto𝕎-chooseT0if : (cc : ContConds) (name : Name) (w : 𝕎·) (r : ren) (n m : ℕ)
                    → upto𝕎 name w (chooseT0if name w n m) r
upto𝕎-chooseT0if cc name w r n m with n <? m
... | yes x =
  mkUpto𝕎
--    (sym (ContConds.ccDchoose≡ cc name w (NUM m)))
--    (sym (ContConds.ccNchoose≡ cc name w (NUM m)))
--    (sameRes-sym (sameRes-chooseT cc name w (NUM m)))
    (upto𝕎getT-chooseT cc name w r (NUM m))
... | no x = mkUpto𝕎 {--refl refl (sameRes-refl w)--} (λ n1 n2 k d1 d2 r → {!!} {--refl--})
--}




-- subRen r1 r2 means that r1 is a sub-renaming of r2
data subRen (l k : List Name) : ren → ren → Set where
  subRen-refl : (r : ren) → subRen l k r r
  subRen-trans : (a b : Name) (r1 r2 : ren)
                 → ¬ a ∈ l -- The new names picked are 'fresh' names
                 → ¬ b ∈ k
                 → subRen l k r1 r2
                 → subRen l k r1 ((a , b) ∷ r2)


presUpdRel2 : (n : ℕ) (name : Name) (f g : Term) (k : ℕ) → Set(lsuc L)
presUpdRel2 n name f g k =
  {a b v : Term} {w0 w1 w2 w : 𝕎·} {r : ren}
  → updRel2 name f g r a b
  → names a ⊆ dom𝕎· w1
  → names b ⊆ dom𝕎· w
  → name ∈ dom𝕎· w
--  → names f ⊆ dom𝕎· w1
--  → names g ⊆ dom𝕎· w
  → upto𝕎 name w1 w r
  → compatible· name w1 Res⊤
  → compatible· name w Res⊤
  → ∀𝕎-get0-NUM w1 name
-- We use ∀𝕎-⇓∼ℕ instead of strongMonEq because if g could change the target world, it could be used for...
--  → ∀𝕎 w (λ w' _ → (k : ℕ) → k < n → ∀𝕎-⇓∼ℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
  → w0 ⊑· w1
  → w0 ⊑· w
  → ∀𝕎 w0 (λ w' _ → (k : ℕ) → k < n → ⇛!sameℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
  → (comp : steps k (a , w1) ≡ (v , w2))
  → isHighestℕ {k} {w1} {w2} {a} {v} n name comp
  → ∈names𝕎 {k} {w1} {w2} {a} {v} name comp
  → isValue v
  → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w' → Σ ren (λ r' →
      steps k' (b , w) ≡ (v' , w')
      × updRel2 name f g r' v v'
      × upto𝕎 name w2 w' r'
      × subRen (dom𝕎· w1) (dom𝕎· w) r r'))))


stepsPresUpdRel2 : (n : ℕ) (name : Name) (f g : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
stepsPresUpdRel2 n name f g b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    Σ (steps k (b , w) ≡ (v , w')) (λ comp →
    isValue v
    × isHighestℕ {k} {w} {w'} {b} {v} n name comp
    × ∈names𝕎 {k} {w} {w'} {b} {v} name comp
    × ((k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k')))))


-- NOTE: We won't be able to prove that for impure terms x because it might read a choice
-- and return 2 different values in the two worlds w2 and w
ΣstepsUpdRel2 : (name : Name) (f g : Term) (x : Term) (w1 w2 : 𝕎·) (b : Term) (w : 𝕎·) (r : ren) → Set(1ℓ Level.⊔ L)
ΣstepsUpdRel2 name f g x w1 w2 b w r =
  Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ Term (λ y1 → Σ Term (λ y2 → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w' → Σ ren (λ r' →
    steps k1 (x , w2) ≡ (y1 , w3)
    × steps k2 (b , w) ≡ (y2 , w')
    × updRel2 name f g r' y1 y2
    × upto𝕎 name w3 w' r'
    × subRen (dom𝕎· w1) (dom𝕎· w) r r')))))))



abstract
  isHighestℕ2-APPLY₂→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {name' : Name} {b v : Term} {w w' : 𝕎·}
                        → (comp : steps k (APPLY (CS name') b , w) ≡ (v , w'))
                        → isValue v
                        → isHighestℕ {k} {w} {w'} {APPLY (CS name') b} {v} n name comp
                        → ∈names𝕎 {k} {w} {w'} {APPLY (CS name') b} {v} name comp
                        → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b , w) ≡ (u , w'')) (λ comp' →
                            isHighestℕ {k'} {w} {w''} {b} {u} n name comp'
                            × ∈names𝕎 {k'} {w} {w''} {b} {u} name comp'
                            × isValue u
                            × k' < k))))
  isHighestℕ2-APPLY₂→ {n} {0} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv h inw
    rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
  isHighestℕ2-APPLY₂→ {n} {suc k} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv h inw with is-NUM b
  ... | inj₁ (j , r) rewrite r with getT j name' w
  ... |    just t = 0 , NUM j , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
  ... |    nothing = 0 , NUM j , w , refl , h , inw , tt , _≤_.s≤s _≤_.z≤n
  isHighestℕ2-APPLY₂→ {n} {suc k} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv h inw | inj₂ r with step⊎ b w
  ... |    inj₁ (b0 , w0 , z) rewrite z = suc (fst ind) , concl
    where
      ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b0 , w0) ≡ (u , w'')) (λ comp' →
                               isHighestℕ {k'} {w0} {w''} {b0} {u} n name comp'
                               × ∈names𝕎 {k'} {w0} {w''} {b0} {u} name comp'
                               × isValue u
                               × k' < k))))
      ind = isHighestℕ2-APPLY₂→ {n} {k} {name} {f} {g} {name'} {b0} {v} {w0} {w'} comp isv (snd h) (snd (snd inw))

      concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (b , w) ≡ (u , w'')) (λ comp' →
                            isHighestℕ {suc (fst ind)} {w} {w''} {b} {u} n name comp'
                            × ∈names𝕎 {suc (fst ind)} {w} {w''} {b} {u} name comp'
                            × isValue u
                            × suc (fst ind) < suc k)))
      concl rewrite z =
        fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
        (fst h , fst (snd (snd (snd (snd ind))))) ,
        (fst inw , fst (snd inw) , fst (snd (snd (snd (snd (snd ind)))))) ,
        fst (snd (snd (snd (snd (snd (snd ind)))))) ,
        _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd ind)))))))
  ... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



abstract
  stepsPresUpdRel2-APPLY₂→ : {n : ℕ} {name : Name} {f g : Term} {name' : Name} {b : Term} {w : 𝕎·}
                             → stepsPresUpdRel2 n name f g (APPLY (CS name') b) w
                             → stepsPresUpdRel2 n name f g b w
  stepsPresUpdRel2-APPLY₂→ {n} {name} {f} {g} {name'} {b} {w} (k , v , w' , comp , isv , ish , inw , ind) =
    fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
    fst (snd (snd (snd (snd (snd (snd hv)))))) , fst (snd (snd (snd (snd hv)))) ,
    fst (snd (snd (snd (snd (snd hv))))) ,
    λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd (snd hv)))))))))
    where
      hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b , w) ≡ (u , w'')) (λ comp' →
                              isHighestℕ {k'} {w} {w''} {b} {u} n name comp'
                              × ∈names𝕎 {k'} {w} {w''} {b} {u} name comp'
                              × isValue u
                              × k' < k))))
      hv = isHighestℕ2-APPLY₂→ {n} {k} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv ish inw


→Σ-steps-APPLY-CS : (n : ℕ) (a b : Term) (w w' : 𝕎·) (name : Name)
                 → steps n (a , w) ≡ (b , w')
                 → Σ ℕ (λ m → steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) b , w'))
→Σ-steps-APPLY-CS n a b w w' name h =
  fst (Σ-steps-APPLY-CS≤ n a b w w' name h) ,
  snd (snd (Σ-steps-APPLY-CS≤ n a b w w' name h))



dren : ren → ren
dren [] = []
dren ((a , b) ∷ r) = (pred a , pred b) ∷ dren r



∈ren-sucIf≤-ren→ : (n name1 name2 : Name) (r : ren)
                    → (sucIf≤ n name1 , sucIf≤ n name2) ∈ sucIf≤-ren n r
                    → (name1 , name2) ∈ r
∈ren-sucIf≤-ren→ n name1 name2 ((a , b) ∷ xs) (here px)
  rewrite sym (sucIf≤-inj {n} {name1} {a} (pair-inj₁ px))
        | sym (sucIf≤-inj {n} {name2} {b} (pair-inj₂ px)) = here refl
∈ren-sucIf≤-ren→ n name1 name2 (x ∷ xs) (there i) = there (∈ren-sucIf≤-ren→ n name1 name2 xs i)



→∈renₗ-sucIf≤-ren : {name : Name} {r : ren} (n : Name)
                    → name ∈ renₗ r
                    → sucIf≤ n name ∈ renₗ (sucIf≤-ren n r)
→∈renₗ-sucIf≤-ren {name} {[]} n ()
→∈renₗ-sucIf≤-ren {name} {(a , b) ∷ r} n (here px) rewrite sym px = here refl
→∈renₗ-sucIf≤-ren {name} {(a , b) ∷ r} n (there i) = there (→∈renₗ-sucIf≤-ren {name} {r} n i)


→∈renᵣ-sucIf≤-ren : {name : Name} {r : ren} (n : Name)
                    → name ∈ renᵣ r
                    → sucIf≤ n name ∈ renᵣ (sucIf≤-ren n r)
→∈renᵣ-sucIf≤-ren {name} {[]} n ()
→∈renᵣ-sucIf≤-ren {name} {(a , b) ∷ r} n (here px) rewrite sym px = here refl
→∈renᵣ-sucIf≤-ren {name} {(a , b) ∷ r} n (there i) = there (→∈renᵣ-sucIf≤-ren {name} {r} n i)


names∈ren-sucIf≤-ren→ : (n name1 name2 : Name) (r : ren)
                         → names∈ren (sucIf≤ n name1) (sucIf≤ n name2) (sucIf≤-ren n r)
                         → names∈ren name1 name2 r
names∈ren-sucIf≤-ren→ n name1 name2 [] e = sucIf≤-inj {n} {name1} {name2} e
names∈ren-sucIf≤-ren→ n name1 name2 ((a , b) ∷ r) (inj₁ (e₁ , e₂)) =
  inj₁ (sucIf≤-inj {n} {name1} {a} e₁ , (sucIf≤-inj {n} {name2} {b} e₂))
names∈ren-sucIf≤-ren→ n name1 name2 ((a , b) ∷ r) (inj₂ (e₁ , e₂ , x)) =
  inj₂ ((λ z → e₁ (→≡sucIf≤ z)) , (λ z → e₂ (→≡sucIf≤ z)) , (names∈ren-sucIf≤-ren→ n name1 name2 r x))



force≡shiftNameUp→ : (v : Var) (name : Name) (g : Term) (b : Term)
                      → LET (VAR 0) (APPLY (shiftNameUp v g) (VAR 0)) ≡ shiftNameUp v b
                      → b ≡ LET (VAR 0) (APPLY g (VAR 0))
force≡shiftNameUp→ v name g (LET (VAR 0) (APPLY b (VAR 0))) e
  rewrite shiftNameUp-inj {v} {g} {b} (APPLYinj1 (LETinj2 e)) = refl



updRel2-shiftNameUp-LAMBDA→ : (v : Name) {name : Name} {f g : Term} (cf : # f) (cg : # g) {r : ren} {a b t u : Term}
                                → t ≡ shiftNameUp v a
                                → u ≡ shiftNameUp v b
                                → updRel2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v g) (sucIf≤-ren v r) (LAMBDA t) u
                                → ((c : Term)
                                    → updRel2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v g) (sucIf≤-ren v r) (shiftNameUp v a) (shiftNameUp v c)
                                    → updRel2 name f g r a c)
                                → updRel2 name f g r (LAMBDA a) b
updRel2-shiftNameUp-LAMBDA→ v {name} {f} {g} cf cg {r} {a} {LAMBDA b} {t} {.(LAMBDA c)} e₁ e₂ (updRel2-LAMBDA .t c u₁) ind rewrite e₁ | LAMinj e₂ = updRel2-LAMBDA _ _ (ind b u₁)
updRel2-shiftNameUp-LAMBDA→ v {name} {f} {g} cf cg {r} {a} {LAMBDA b} {.(updBody (sucIf≤ v name) (shiftNameUp v f))} {.(force (shiftNameUp v g))} e₁ e₂ updRel2-upd ind
  rewrite updBody≡shiftNameUp→ v name f a e₁
        | force≡shiftNameUp→ v name g b (LAMinj e₂) = updRel2-upd

\end{code}
