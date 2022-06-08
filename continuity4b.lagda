\begin{code}
{-# OPTIONS --rewriting #-}
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


module continuity4b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
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

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)



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


data updRel2 (name : Name) (f g : Term) : Term → Term → Set where
  updRel2-VAR     : (x : Var) → updRel2 name f g (VAR x) (VAR x)
  updRel2-NAT     : updRel2 name f g NAT NAT
  updRel2-QNAT    : updRel2 name f g QNAT QNAT
  updRel2-TNAT    : updRel2 name f g TNAT TNAT
  updRel2-LT      : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (LT a₁ b₁) (LT a₂ b₂)
  updRel2-QLT     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (QLT a₁ b₁) (QLT a₂ b₂)
  updRel2-NUM     : (x : ℕ) → updRel2 name f g (NUM x) (NUM x)
  updRel2-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g c₁ c₂ → updRel2 name f g d₁ d₂ → updRel2 name f g (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  updRel2-SUC     : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (SUC a₁) (SUC a₂)
  updRel2-PI      : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (PI a₁ b₁) (PI a₂ b₂)
  updRel2-LAMBDA  : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (LAMBDA a₁) (LAMBDA a₂)
  updRel2-APPLY   : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (APPLY a₁ b₁) (APPLY a₂ b₂)
  updRel2-FIX     : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (FIX a₁) (FIX a₂)
  updRel2-LET     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (LET a₁ b₁) (LET a₂ b₂)
  updRel2-SUM     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (SUM a₁ b₁) (SUM a₂ b₂)
  updRel2-PAIR    : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (PAIR a₁ b₁) (PAIR a₂ b₂)
  updRel2-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  updRel2-SET     : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (SET a₁ b₁) (SET a₂ b₂)
  updRel2-ISECT   : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (ISECT a₁ b₁) (ISECT a₂ b₂)
  updRel2-TUNION  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (TUNION a₁ b₁) (TUNION a₂ b₂)
  updRel2-UNION   : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (UNION a₁ b₁) (UNION a₂ b₂)
  updRel2-QTUNION : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  updRel2-INL     : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (INL a₁) (INL a₂)
  updRel2-INR     : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (INR a₁) (INR a₂)
  updRel2-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g c₁ c₂ → updRel2 name f g (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  updRel2-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g c₁ c₂ → updRel2 name f g (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  updRel2-AX      : updRel2 name f g AX AX
  updRel2-FREE    : updRel2 name f g FREE FREE
  updRel2-CS      : (name' : Name) → ¬ name' ≡ name → updRel2 name f g (CS name') (CS name')
  updRel2-NAME    : (name' : Name) → ¬ name' ≡ name → updRel2 name f g (NAME name') (NAME name')
  updRel2-FRESH   : (a b : Term) → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) a b → updRel2 name f g (FRESH a) (FRESH b)
  updRel2-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  updRel2-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel2 name1 name2 f a₁ a₂ → updRel2 name1 name2 f b₁ b₂ → updRel2 name1 name2 f c₁ c₂ → updRel2 name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updRel2-TSQUASH : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (TSQUASH a₁) (TSQUASH a₂)
  updRel2-TTRUNC  : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (TTRUNC a₁) (TTRUNC a₂)
  updRel2-TCONST  : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (TCONST a₁) (TCONST a₂)
  updRel2-SUBSING : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (SUBSING a₁) (SUBSING a₂)
  updRel2-PURE    : updRel2 name f g PURE PURE
  updRel2-DUM     : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (DUM a₁) (DUM a₂)
  updRel2-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g b₁ b₂ → updRel2 name f g (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  updRel2-UNIV    : (x : ℕ) → updRel2 name f g (UNIV x) (UNIV x)
  updRel2-LIFT    : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (LIFT a₁) (LIFT a₂)
  updRel2-LOWER   : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (LOWER a₁) (LOWER a₂)
  updRel2-SHRINK  : (a₁ a₂ : Term) → updRel2 name f g a₁ a₂ → updRel2 name f g (SHRINK a₁) (SHRINK a₂)
  updRel2-upd     : updRel2 name f g (upd name f) (force g)


upto𝕎getT : (name : Name) (w1 w2 : 𝕎·) → Set
upto𝕎getT name w1 w2 = (n : Name) (k : ℕ) → ¬ n ≡ name → getT k n w1 ≡ getT k n w2


upto𝕎 : (name : Name) (w1 w2 : 𝕎·) → Set
upto𝕎 name w1 w2 =
  dom𝕎· w1 ≡ dom𝕎· w2
  × names𝕎· w1 ≡ names𝕎· w2
  × upto𝕎getT name w1 w2


upto𝕎-sym : (name : Name) (w1 w2 : 𝕎·) → upto𝕎 name w1 w2 → upto𝕎 name w2 w1
upto𝕎-sym name w1 w2 (eqd , eqn , u) = sym eqd , sym eqn , λ n k d → sym (u n k d)


upto𝕎-trans : (name : Name) (w1 w2 w3 : 𝕎·) → upto𝕎 name w1 w2 → upto𝕎 name w2 w3 → upto𝕎 name w1 w3
upto𝕎-trans name w1 w2 w3 (eqd1 , eqn1 , u1) (eqd2 , eqn2 , u2) =
  trans eqd1 eqd2 , trans eqn1 eqn2 , λ  n k d → trans (u1 n k d) (u2 n k d)


upto𝕎getT-chooseT : (cc : ContConds) (name : Name) (w : 𝕎·) (t : Term)
                     → upto𝕎getT name w (chooseT name w t)
upto𝕎getT-chooseT cc name w t nm k d =
  sym (ContConds.ccGcd cc k nm name w t d)


upto𝕎-chooseT0if : (cc : ContConds) (name : Name) (w : 𝕎·) (n m : ℕ)
                    → upto𝕎 name w (chooseT0if name w n m)
upto𝕎-chooseT0if cc name w n m with n <? m
... | yes x =
  sym (ContConds.ccDchoose≡ cc name w (NUM m)) ,
  sym (ContConds.ccNchoose≡ cc name w (NUM m) refl) ,
  upto𝕎getT-chooseT cc name w (NUM m)
... | no x = refl , refl , λ nm k d → refl


presUpdRel2 : (n : ℕ) (name : Name) (f g : Term) (k : ℕ) → Set(lsuc L)
presUpdRel2 n name f g k =
  {a b v : Term} {w1 w2 w : 𝕎·}
  → updRel2 name f g a b
  → upto𝕎 name w1 w
  → compatible· name w1 Res⊤
  → compatible· name w Res⊤
  → ∀𝕎-get0-NUM w1 name
-- We use ∀𝕎-⇓∼ℕ instead of strongMonEq because if g could change the target world, it could be used for...
  → ∀𝕎 w (λ w' _ → (k : ℕ) → k < n → ∀𝕎-⇓∼ℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
  → (comp : steps k (a , w1) ≡ (v , w2))
  → isHighestℕ {k} {w1} {w2} {a} {v} n name comp
  → ∈names𝕎 {k} {w1} {w2} {a} {v} name comp
  → isValue v
  → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w' →
      steps k' (b , w) ≡ (v' , w')
      × updRel2 name f g v v'
      × upto𝕎 name w2 w')))


stepsPresUpdRel2 : (n : ℕ) (name : Name) (f g : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
stepsPresUpdRel2 n name f g b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    Σ (steps k (b , w) ≡ (v , w')) (λ comp →
    isValue v
    × isHighestℕ {k} {w} {w'} {b} {v} n name comp
    × ∈names𝕎 {k} {w} {w'} {b} {v} name comp
    × ((k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k')))))


updRel2-NUMₗ→ : {name : Name} {f g : Term} {n : ℕ} {a : Term}
               → updRel2 name f g (NUM n) a
               → a ≡ NUM n
updRel2-NUMₗ→ {name} {f} {g} {n} {.(NUM n)} (updRel2-NUM .n) = refl


updRel2-CSₗ→ : {name : Name} {f g : Term} {n : Name} {a : Term}
               → updRel2 name f g (CS n) a
               → a ≡ CS n
updRel2-CSₗ→ {name} {f} {g} {n} {.(CS n)} (updRel2-CS .n x) = refl


updRel2-CSₗ→¬≡ : {name : Name} {f g : Term} {n : Name} {a : Term}
               → updRel2 name f g (CS n) a
               → ¬ n ≡ name
updRel2-CSₗ→¬≡ {name} {f} {g} {n} {.(CS n)} (updRel2-CS .n x) = x


-- NOTE: We won't be able to prove that for impure terms x because it might read a choice
-- and return 2 different values in the two worlds w2 and w
ΣstepsUpdRel2 : (name : Name) (f g : Term) (x : Term) (w2 : 𝕎·) (b : Term) (w : 𝕎·) → Set(L)
ΣstepsUpdRel2 name f g x w2 b w =
  Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ Term (λ y1 → Σ Term (λ y2 → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w' →
    steps k1 (x , w2) ≡ (y1 , w3)
    × steps k2 (b , w) ≡ (y2 , w')
    × updRel2 name f g y1 y2
    × upto𝕎 name w3 w'))))))



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


updRel2-refl : {name : Name} {f g : Term} {a : Term}
               → ¬ name ∈ names a
               → updRel2 name f g a a
updRel2-refl {name} {f} {g} {VAR x} nn = updRel2-VAR _
updRel2-refl {name} {f} {g} {NAT} nn = updRel2-NAT
updRel2-refl {name} {f} {g} {QNAT} nn = updRel2-QNAT
updRel2-refl {name} {f} {g} {TNAT} nn = updRel2-TNAT
updRel2-refl {name} {f} {g} {LT a a₁} nn = updRel2-LT _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {QLT a a₁} nn = updRel2-QLT _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {NUM x} nn = updRel2-NUM _
updRel2-refl {name} {f} {g} {IFLT a a₁ a₂ a₃} nn = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++4→¬∈2 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn)) (updRel2-refl {name} {f} {g} {a₂} (¬∈++4→¬∈3 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn)) (updRel2-refl {name} {f} {g} {a₃} (¬∈++4→¬∈4 {_} {_} {names a} {names a₁} {names a₂} {names a₃} nn))
updRel2-refl {name} {f} {g} {SUC a} nn = updRel2-SUC _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {PI a a₁} nn = updRel2-PI _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {LAMBDA a} nn = updRel2-LAMBDA _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {APPLY a a₁} nn = updRel2-APPLY _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {FIX a} nn = updRel2-FIX _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {LET a a₁} nn = updRel2-LET _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {SUM a a₁} nn = updRel2-SUM _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {PAIR a a₁} nn = updRel2-PAIR _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {SPREAD a a₁} nn = updRel2-SPREAD _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {SET a a₁} nn = updRel2-SET _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {TUNION a a₁} nn = updRel2-TUNION _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {ISECT a a₁} nn = updRel2-ISECT _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {UNION a a₁} nn = updRel2-UNION _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {QTUNION a a₁} nn = updRel2-QTUNION _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {INL a} nn = updRel2-INL _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {INR a} nn = updRel2-INR _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {DECIDE a a₁ a₂} nn = updRel2-DECIDE _ _ _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++3→¬∈2 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {a₂} (¬∈++3→¬∈3 {_} {_} {names a} {names a₁} {names a₂} nn))
updRel2-refl {name} {f} {g} {EQ a a₁ a₂} nn = updRel2-EQ _ _ _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++3→¬∈2 {_} {_} {names a} {names a₁} {names a₂} nn)) (updRel2-refl {name} {f} {g} {a₂} (¬∈++3→¬∈3 {_} {_} {names a} {names a₁} {names a₂} nn))
updRel2-refl {name} {f} {g} {AX} nn = updRel2-AX
updRel2-refl {name} {f} {g} {FREE} nn = updRel2-FREE
updRel2-refl {name} {f} {g} {CS x} nn = updRel2-CS _ λ z → nn (here (sym z))
updRel2-refl {name} {f} {g} {NAME x} nn = updRel2-NAME _ λ z → nn (here (sym z))
updRel2-refl {name} {f} {g} {FRESH a} nn = updRel2-FRESH _ _ (updRel2-refl {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {a} λ z → nn (suc→∈lowerNames {name} {names a} z))
updRel2-refl {name} {f} {g} {CHOOSE a a₁} nn = updRel2-CHOOSE _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {TSQUASH a} nn = updRel2-TSQUASH _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {TTRUNC a} nn = updRel2-TTRUNC _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {TCONST a} nn = updRel2-TCONST _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {SUBSING a} nn = updRel2-SUBSING _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {DUM a} nn = updRel2-DUM _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {FFDEFS a a₁} nn = updRel2-FFDEFS _ _ _ _ (updRel2-refl {name} {f} {g} {a} (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} nn)) (updRel2-refl {name} {f} {g} {a₁} (¬∈++2→¬∈2 {_} {_} {names a} {names a₁} nn))
updRel2-refl {name} {f} {g} {PURE} nn = updRel2-PURE
updRel2-refl {name} {f} {g} {UNIV x} nn = updRel2-UNIV _
updRel2-refl {name} {f} {g} {LIFT a} nn = updRel2-LIFT _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {LOWER a} nn = updRel2-LOWER _ _ (updRel2-refl {name} {f} {g} {a} nn)
updRel2-refl {name} {f} {g} {SHRINK a} nn = updRel2-SHRINK _ _ (updRel2-refl {name} {f} {g} {a} nn)



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
                        → updRel2 name f g b₁ b₂
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



updRel2-LAMBDAₗ→ : {name : Name} {f g : Term} {t : Term} {a : Term}
                  → updRel2 name f g (LAMBDA t) a
                  → Σ Term (λ u → a ≡ LAMBDA u × updRel2 name f g t u)
                     ⊎ (t ≡ updBody name f × a ≡ force g)
updRel2-LAMBDAₗ→ {name} {f} {g} {t} {.(LAMBDA a₂)} (updRel2-LAMBDA .t a₂ u) = inj₁ (a₂ , refl , u)
updRel2-LAMBDAₗ→ {name} {f} {g} {.(updBody name f)} {.(force g)} updRel2-upd = inj₂ (refl , refl)



updRel2-PAIRₗ→ : {name : Name} {f g : Term} {t₁ t₂ : Term} {a : Term}
                → updRel2 name f g (PAIR t₁ t₂) a
                → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ PAIR u₁ u₂ × updRel2 name f g t₁ u₁ × updRel2 name f g t₂ u₂))
updRel2-PAIRₗ→ {name} {f} {g} {t₁} {t₂} {.(PAIR a₁ a₂)} (updRel2-PAIR .t₁ a₁ .t₂ a₂ u1 u2) = a₁ , a₂ , refl , u1 , u2



updRel2-INLₗ→ : {name : Name} {f g : Term} {t : Term} {a : Term}
                → updRel2 name f g (INL t) a
                → Σ Term (λ u → a ≡ INL u × updRel2 name f g t u)
updRel2-INLₗ→ {name} {f} {g} {t} {.(INL x)} (updRel2-INL .t x u) = x , refl , u



updRel2-INRₗ→ : {name : Name} {f g : Term} {t : Term} {a : Term}
                → updRel2 name f g (INR t) a
                → Σ Term (λ u → a ≡ INR u × updRel2 name f g t u)
updRel2-INRₗ→ {name} {f} {g} {t} {.(INR x)} (updRel2-INR .t x u) = x , refl , u



Σsteps-updRel2-NUM→ : {name : Name} {f g : Term} {m : ℕ} {b : Term} {w1 : 𝕎·} {w2 : 𝕎·}
                      → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w1' → steps k' (b , w1) ≡ (v' , w1') × updRel2 name f g (NUM m) v' × upto𝕎 name w2 w1')))
                      → Σ ℕ (λ k' → Σ 𝕎· (λ w1' → steps k' (b , w1) ≡ (NUM m , w1') × upto𝕎 name w2 w1'))
Σsteps-updRel2-NUM→ {name} {f} {g} {m} {b} {w1} {w2} (k' , .(NUM m) , w1' , comp , updRel2-NUM .m , upw) = k' , w1' , comp , upw



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


updRel2-shiftUp : (n : ℕ) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a b : Term}
                 → updRel2 name f g a b
                 → updRel2 name f g (shiftUp n a) (shiftUp n b)
updRel2-shiftUp n {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} (updRel2-VAR x) = updRel2-VAR _
updRel2-shiftUp n {name} {f} {g} cf cg {.NAT} {.NAT} updRel2-NAT = updRel2-NAT
updRel2-shiftUp n {name} {f} {g} cf cg {.QNAT} {.QNAT} updRel2-QNAT = updRel2-QNAT
updRel2-shiftUp n {name} {f} {g} cf cg {.TNAT} {.TNAT} updRel2-TNAT = updRel2-TNAT
updRel2-shiftUp n {name} {f} {g} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} (updRel2-NUM x) = updRel2-NUM _
updRel2-shiftUp n {name} {f} {g} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁) (updRel2-shiftUp n cf cg u₂) (updRel2-shiftUp n cf cg u₃)
updRel2-shiftUp n {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-shiftUp (suc n) cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc (suc n)) cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp (suc n) cf cg u₁) (updRel2-shiftUp (suc n) cf cg u₂)
updRel2-shiftUp n {name} {f} {g} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁) (updRel2-shiftUp n cf cg u₂)
updRel2-shiftUp n {name} {f} {g} cf cg {.AX} {.AX} updRel2-AX = updRel2-AX
updRel2-shiftUp n {name} {f} {g} cf cg {.FREE} {.FREE} updRel2-FREE = updRel2-FREE
updRel2-shiftUp n {name} {f} {g} cf cg {.(CS name')} {.(CS name')} (updRel2-CS name' x) = updRel2-CS _ x
updRel2-shiftUp n {name} {f} {g} cf cg {.(NAME name')} {.(NAME name')} (updRel2-NAME name' x) = updRel2-NAME _ x
updRel2-shiftUp n {name} {f} {g} cf cg {.(FRESH a₁)} {.(FRESH a₂)} (updRel2-FRESH a₁ a₂ r) = updRel2-FRESH _ _ (updRel2-shiftUp n (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) r)
updRel2-shiftUp n {name} {f} {g} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(PURE)} {.(PURE)} (updRel2-PURE) = updRel2-PURE
updRel2-shiftUp n {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftUp n cf cg u) (updRel2-shiftUp n cf cg u₁)
updRel2-shiftUp n {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} (updRel2-UNIV x) = updRel2-UNIV x
updRel2-shiftUp n {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-shiftUp n cf cg u)
updRel2-shiftUp n {name} {f} {g} cf cg {.(upd name f)} {.(force g)} updRel2-upd
  rewrite #shiftUp (suc (suc n)) (ct g cg)
        | #shiftUp (suc (suc (suc n))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updRel2-upd



updRel2-shiftDown : (n : ℕ) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a b : Term}
                 → updRel2 name f g a b
                 → updRel2 name f g (shiftDown n a) (shiftDown n b)
updRel2-shiftDown n {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} (updRel2-VAR x) = updRel2-VAR _
updRel2-shiftDown n {name} {f} {g} cf cg {.NAT} {.NAT} updRel2-NAT = updRel2-NAT
updRel2-shiftDown n {name} {f} {g} cf cg {.QNAT} {.QNAT} updRel2-QNAT = updRel2-QNAT
updRel2-shiftDown n {name} {f} {g} cf cg {.TNAT} {.TNAT} updRel2-TNAT = updRel2-TNAT
updRel2-shiftDown n {name} {f} {g} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} (updRel2-NUM x) = updRel2-NUM _
updRel2-shiftDown n {name} {f} {g} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁) (updRel2-shiftDown n cf cg u₂) (updRel2-shiftDown n cf cg u₃)
updRel2-shiftDown n {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-shiftDown (suc n) cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc (suc n)) cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown (suc n) cf cg u₁) (updRel2-shiftDown (suc n) cf cg u₂)
updRel2-shiftDown n {name} {f} {g} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁) (updRel2-shiftDown n cf cg u₂)
updRel2-shiftDown n {name} {f} {g} cf cg {.AX} {.AX} updRel2-AX = updRel2-AX
updRel2-shiftDown n {name} {f} {g} cf cg {.FREE} {.FREE} updRel2-FREE = updRel2-FREE
updRel2-shiftDown n {name} {f} {g} cf cg {.(CS name')} {.(CS name')} (updRel2-CS name' x) = updRel2-CS _ x
updRel2-shiftDown n {name} {f} {g} cf cg {.(NAME name')} {.(NAME name')} (updRel2-NAME name' x) = updRel2-NAME _ x
updRel2-shiftDown n {name} {f} {g} cf cg {.(FRESH a₁)} {.(FRESH a₂)} (updRel2-FRESH a₁ a₂ r) = updRel2-FRESH _ _ (updRel2-shiftDown n (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) r)
updRel2-shiftDown n {name} {f} {g} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(PURE)} {.(PURE)} (updRel2-PURE) = updRel2-PURE
updRel2-shiftDown n {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftDown n cf cg u) (updRel2-shiftDown n cf cg u₁)
updRel2-shiftDown n {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} (updRel2-UNIV x) = updRel2-UNIV _
updRel2-shiftDown n {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-shiftDown n cf cg u)
updRel2-shiftDown n {name} {f} {g} cf cg {.(upd name f)} {.(force g)} updRel2-upd
  rewrite #shiftDown (suc (suc n)) (ct g cg)
        | #shiftDown (suc (suc (suc n))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updRel2-upd



updRel2-shiftNameUp : (n : ℕ) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a b : Term}
                 → updRel2 name f g a b
                 → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (shiftNameUp n a) (shiftNameUp n b)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} (updRel2-VAR x) = updRel2-VAR _
updRel2-shiftNameUp n {name} {f} {g} cf cg {.NAT} {.NAT} updRel2-NAT = updRel2-NAT
updRel2-shiftNameUp n {name} {f} {g} cf cg {.QNAT} {.QNAT} updRel2-QNAT = updRel2-QNAT
updRel2-shiftNameUp n {name} {f} {g} cf cg {.TNAT} {.TNAT} updRel2-TNAT = updRel2-TNAT
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} (updRel2-NUM x) = updRel2-NUM _
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂) (updRel2-shiftNameUp n cf cg u₃)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁) (updRel2-shiftNameUp n cf cg u₂)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.AX} {.AX} updRel2-AX = updRel2-AX
updRel2-shiftNameUp n {name} {f} {g} cf cg {.FREE} {.FREE} updRel2-FREE = updRel2-FREE
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(CS name')} {.(CS name')} (updRel2-CS name' x) = updRel2-CS _ (λ z → x (sucIf≤-inj z))
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(NAME name')} {.(NAME name')} (updRel2-NAME name' x) = updRel2-NAME _ (λ z → x (sucIf≤-inj z))
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(FRESH a₁)} {.(FRESH a₂)} (updRel2-FRESH a₁ a₂ r) = updRel2-FRESH (shiftNameUp (suc n) a₁) (shiftNameUp (suc n) a₂) c1
  where
    c3 : updRel2 (sucIf≤ (suc n) (suc name))
                (shiftNameUp (suc n) (shiftNameUp 0 f))
                (shiftNameUp (suc n) (shiftNameUp 0 g))
                (shiftNameUp (suc n) a₁)
                (shiftNameUp (suc n) a₂)
    c3 = updRel2-shiftNameUp (suc n) {suc name} (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) r

    c2 : updRel2 (suc (sucIf≤ n name))
                (shiftNameUp (suc n) (shiftNameUp 0 f))
                (shiftNameUp (suc n) (shiftNameUp 0 g))
                (shiftNameUp (suc n) a₁)
                (shiftNameUp (suc n) a₂)
    c2 rewrite suc-sucIf≤ n name = c3

    c1 : updRel2 (suc (sucIf≤ n name))
                (shiftNameUp 0 (shiftNameUp n f))
                (shiftNameUp 0 (shiftNameUp n g))
                (shiftNameUp (suc n) a₁)
                (shiftNameUp (suc n) a₂)
    c1 rewrite shiftNameUp-shiftNameUp {0} {n} {f} _≤_.z≤n | shiftNameUp-shiftNameUp {0} {n} {g} _≤_.z≤n = c2
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(PURE)} {.(PURE)} (updRel2-PURE) = updRel2-PURE
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftNameUp n cf cg u) (updRel2-shiftNameUp n cf cg u₁)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} (updRel2-UNIV x) = updRel2-UNIV x
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-shiftNameUp n cf cg u)
updRel2-shiftNameUp n {name} {f} {g} cf cg {.(upd name f)} {.(force g)} updRel2-upd = c2
  where
    c1 : updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (upd (sucIf≤ n name) (shiftNameUp n f)) (force (shiftNameUp n g))
    c1 = updRel2-upd

    c2 : updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g)
                (LAMBDA (LET (VAR 0)
                             (LET (IFLT (APPLY (CS (sucIf≤ n name)) (NUM 0)) (VAR 0)
                                        (CHOOSE (NAME (sucIf≤ n name)) (VAR 0)) AX)
                                  (APPLY (shiftNameUp n (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
                (LAMBDA (LET (VAR 0) (APPLY (shiftNameUp n g) (VAR 0))))
    c2 rewrite sym (shiftUp-shiftNameUp 0 n f) = c1



updRel2-shiftNameUp0 : {name : Name} {f g : Term} (cf : # f) (cg : # g) {a b : Term}
                   → updRel2 name f g a b
                   → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) (shiftNameUp 0 a) (shiftNameUp 0 b)
updRel2-shiftNameUp0 {name} {f} {g} cf cg {a} {b} u
  rewrite suc≡sucIf≤0 name =
  updRel2-shiftNameUp 0 {name} cf cg u



updRel2-subv : (v : Var) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a₁ a₂ b₁ b₂ : Term}
              → updRel2 name f g a₁ a₂
              → updRel2 name f g b₁ b₂
              → updRel2 name f g (subv v b₁ a₁) (subv v b₂ a₂)
updRel2-subv v {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} {b₁} {b₂} (updRel2-VAR x) ub with x ≟ v
... | yes p = ub
... | no p = updRel2-VAR x
updRel2-subv v {name} {f} {g} cf cg {.NAT} {.NAT} {b₁} {b₂} updRel2-NAT ub = updRel2-NAT
updRel2-subv v {name} {f} {g} cf cg {.QNAT} {.QNAT} {b₁} {b₂} updRel2-QNAT ub = updRel2-QNAT
updRel2-subv v {name} {f} {g} cf cg {.TNAT} {.TNAT} {b₁} {b₂} updRel2-TNAT ub = updRel2-TNAT
updRel2-subv v {name} {f} {g} cf cg {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (updRel2-LT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-LT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (updRel2-QLT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-QLT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} {b₁} {b₂} (updRel2-NUM x) ub = updRel2-NUM x
updRel2-subv v {name} {f} {g} cf cg {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₂)} {b₁} {b₂} (updRel2-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub) (updRel2-subv v cf cg ua₂ ub) (updRel2-subv v cf cg ua₃ ub)
updRel2-subv v {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} {b₁} {b₂} (updRel2-SUC a₁ a₂ ua) ub = updRel2-SUC _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (updRel2-PI a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-PI _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} {b₁} {b₂} (updRel2-LAMBDA a₁ a₂ ua) ub = updRel2-LAMBDA _ _ (updRel2-subv (suc v) cf cg ua (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (updRel2-APPLY a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-APPLY _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} {b₁} {b₂} (updRel2-FIX a₁ a₂ ua) ub = updRel2-FIX _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (updRel2-LET a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-LET _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (updRel2-SUM a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SUM _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (updRel2-PAIR a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-PAIR _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (updRel2-SPREAD a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SPREAD _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc (suc v)) cf cg ua₁ (updRel2-shiftUp 0 cf cg (updRel2-shiftUp 0 cf cg ub)))
updRel2-subv v {name} {f} {g} cf cg {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (updRel2-SET a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-SET _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(ISECT a₁ b₃)} {.(ISECT a₂ b₄)} {b₁} {b₂} (updRel2-ISECT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-ISECT _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (updRel2-TUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-TUNION _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (updRel2-UNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-UNION _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (updRel2-QTUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-QTUNION _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} {b₁} {b₂} (updRel2-INL a₁ a₂ ua) ub = updRel2-INL _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} {b₁} {b₂} (updRel2-INR a₁ a₂ ua) ub = updRel2-INR _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (updRel2-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updRel2-DECIDE _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv (suc v) cf cg ua₁ (updRel2-shiftUp 0 cf cg ub)) (updRel2-subv (suc v) cf cg ua₂ (updRel2-shiftUp 0 cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (updRel2-EQ a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updRel2-EQ _ _ _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub) (updRel2-subv v cf cg ua₂ ub)
updRel2-subv v {name} {f} {g} cf cg {.AX} {.AX} {b₁} {b₂} updRel2-AX ub = updRel2-AX
updRel2-subv v {name} {f} {g} cf cg {.FREE} {.FREE} {b₁} {b₂} updRel2-FREE ub = updRel2-FREE
updRel2-subv v {name} {f} {g} cf cg {.(CS name')} {.(CS name')} {b₁} {b₂} (updRel2-CS name' x) ub = updRel2-CS _ x
updRel2-subv v {name} {f} {g} cf cg {.(NAME name')} {.(NAME name')} {b₁} {b₂} (updRel2-NAME name' x) ub = updRel2-NAME _ x
updRel2-subv v {name} {f} {g} cf cg {.(FRESH a₁)} {.(FRESH a₂)} {b₁} {b₂} (updRel2-FRESH a₁ a₂ ua) ub = updRel2-FRESH _ _ (updRel2-subv v {suc name} (→#shiftNameUp 0 {f} cf) (→#shiftNameUp 0 {g} cg) {a₁} {a₂} {shiftNameUp 0 b₁} {shiftNameUp 0 b₂} ua (updRel2-shiftNameUp0 {name} cf cg ub))
updRel2-subv v {name} {f} {g} cf cg {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (updRel2-CHOOSE a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-CHOOSE _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} {b₁} {b₂} (updRel2-TSQUASH a₁ a₂ ua) ub = updRel2-TSQUASH _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} {b₁} {b₂} (updRel2-TTRUNC a₁ a₂ ua) ub = updRel2-TTRUNC _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} {b₁} {b₂} (updRel2-TCONST a₁ a₂ ua) ub = updRel2-TCONST _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} {b₁} {b₂} (updRel2-SUBSING a₁ a₂ ua) ub = updRel2-SUBSING _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(PURE)} {.(PURE)} {b₁} {b₂} (updRel2-PURE) ub = updRel2-PURE
updRel2-subv v {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} {b₁} {b₂} (updRel2-DUM a₁ a₂ ua) ub = updRel2-DUM _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (updRel2-FFDEFS a₁ a₂ b₃ b₄ ua ua₁) ub = updRel2-FFDEFS _ _ _ _ (updRel2-subv v cf cg ua ub) (updRel2-subv v cf cg ua₁ ub)
updRel2-subv v {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (updRel2-UNIV x) ub = updRel2-UNIV x
updRel2-subv v {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} {b₁} {b₂} (updRel2-LIFT a₁ a₂ ua) ub = updRel2-LIFT _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} {b₁} {b₂} (updRel2-LOWER a₁ a₂ ua) ub = updRel2-LOWER _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} {b₁} {b₂} (updRel2-SHRINK a₁ a₂ ua) ub = updRel2-SHRINK _ _ (updRel2-subv v cf cg ua ub)
updRel2-subv v {name} {f} {g} cf cg {.(upd name f)} {.(force g)} {b₁} {b₂} updRel2-upd ub
  rewrite subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₁))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
        | subv# (suc (suc v)) (shiftUp 0 (shiftUp 0 b₂)) g cg
  = updRel2-upd



updRel2-sub : {name : Name} {f g : Term} (cf : # f) (cg : # g) {a₁ a₂ b₁ b₂ : Term}
             → updRel2 name f g a₁ a₂
             → updRel2 name f g b₁ b₂
             → updRel2 name f g (sub b₁ a₁) (sub b₂ a₂)
updRel2-sub {name} {f} {g} cf cg {a₁} {a₂} {b₁} {b₂} ua ub =
  updRel2-shiftDown 0 cf cg (updRel2-subv 0 cf cg ua (updRel2-shiftUp 0 cf cg ub))

\end{code}
