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


module continuity2b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)



data updCtxt2 (name : Name) (f : Term) : Term → Set where
  updCtxt2-VAR     : (x : Var) → updCtxt2 name f (VAR x)
  updCtxt2-NAT     : updCtxt2 name f NAT
  updCtxt2-QNAT    : updCtxt2 name f QNAT
  updCtxt2-LT      : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (LT a b)
  updCtxt2-QLT     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (QLT a b)
  updCtxt2-NUM     : (x : ℕ) → updCtxt2 name f (NUM x)
  updCtxt2-IFLT    : (a b c d : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f d → updCtxt2 name f (IFLT a b c d)
  updCtxt2-SUC     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SUC a)
  updCtxt2-PI      : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (PI a b)
  updCtxt2-LAMBDA  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LAMBDA a)
  updCtxt2-APPLY   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (APPLY a b)
  updCtxt2-FIX     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (FIX a)
  updCtxt2-LET     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (LET a b)
  updCtxt2-SUM     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SUM a b)
  updCtxt2-PAIR    : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (PAIR a b)
  updCtxt2-SPREAD  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SPREAD a b)
  updCtxt2-SET     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SET a b)
  updCtxt2-ISECT   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (ISECT a b)
  updCtxt2-TUNION  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (TUNION a b)
  updCtxt2-UNION   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (UNION a b)
  updCtxt2-QTUNION : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (QTUNION a b)
  updCtxt2-INL     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (INL a)
  updCtxt2-INR     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (INR a)
  updCtxt2-DECIDE  : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (DECIDE a b c)
  updCtxt2-EQ      : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (EQ a b c)
  updCtxt2-AX      : updCtxt2 name f AX
  updCtxt2-FREE    : updCtxt2 name f FREE
  updCtxt2-CS      : (name' : Name) → updCtxt2 name f (CS name')
  updCtxt2-NAME    : (name' : Name) → ¬ name' ≡ name → updCtxt2 name f (NAME name')
  updCtxt2-FRESH   : (a : Term) → updCtxt2 (suc name) (shiftNameUp 0 f) a → updCtxt2 name f (FRESH a)
  updCtxt2-CHOOSE  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (CHOOSE a b)
--  updCtxt2-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updCtxt2 name1 name2 f a₁ a₂ → updCtxt2 name1 name2 f b₁ b₂ → updCtxt2 name1 name2 f c₁ c₂ → updCtxt2 name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updCtxt2-TSQUASH : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TSQUASH a)
  updCtxt2-TTRUNC  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TTRUNC a)
  updCtxt2-TCONST  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TCONST a)
  updCtxt2-SUBSING : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SUBSING a)
  updCtxt2-PURE    : updCtxt2 name f PURE
  updCtxt2-DUM     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (DUM a)
  updCtxt2-FFDEFS  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (FFDEFS a b)
  updCtxt2-UNIV    : (x : ℕ) → updCtxt2 name f (UNIV x)
  updCtxt2-LIFT    : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LIFT a)
  updCtxt2-LOWER   : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LOWER a)
  updCtxt2-SHRINK  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SHRINK a)
  updCtxt2-upd     : updCtxt2 name f (upd name f)



∈names𝕎 : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (name : Name)
              → steps k (a , w1) ≡ (b , w2)
              → Set
∈names𝕎 {0} {w1} {w2} {a} {b} name comp = ¬ name ∈ names𝕎· w1 × name ∈ dom𝕎· w1
∈names𝕎 {suc k} {w1} {w2} {a} {b} name comp with step a w1
... | just (x , w) = ¬ name ∈ names𝕎· w1 × name ∈ dom𝕎· w1 × ∈names𝕎 {k} {w} {w2} {x} {b} name comp
... | nothing = ¬ name ∈ names𝕎· w1 × name ∈ dom𝕎· w1


pres∈names𝕎 : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (name : Name) (comp : steps k (a , w1) ≡ (b , w2)) → Set
pres∈names𝕎 {k} {w1} {w2} {a} {b} name comp =
  ¬ name ∈ names𝕎· w1
  → name ∈ dom𝕎· w1
  → ∈names𝕎 {k} {w1} {w2} {a} {b} name comp


∈names𝕎→¬∈name𝕎 : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (name : Name)
                     (comp : steps k (a , w1) ≡ (b , w2))
                     → ∈names𝕎 {k} {w1} {w2} {a} {b} name comp
                     → ¬ name ∈ names𝕎· w1
∈names𝕎→¬∈name𝕎 {0} {w1} {w2} {a} {b} name comp inw = fst inw
∈names𝕎→¬∈name𝕎 {suc k} {w1} {w2} {a} {b} name comp inw with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = fst inw
... | inj₂ z rewrite z = fst inw



∈names𝕎→∈dom𝕎 : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (name : Name)
                     (comp : steps k (a , w1) ≡ (b , w2))
                     → ∈names𝕎 {k} {w1} {w2} {a} {b} name comp
                     → name ∈ dom𝕎· w1
∈names𝕎→∈dom𝕎 {0} {w1} {w2} {a} {b} name comp inw = snd inw
∈names𝕎→∈dom𝕎 {suc k} {w1} {w2} {a} {b} name comp inw with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = fst (snd inw)
... | inj₂ z rewrite z = snd inw


presHighestℕ2 : (name : Name) (f : Term) (k : ℕ) → Set(lsuc L)
presHighestℕ2 name f k =
  {w1 w2 : 𝕎·} {a b : Term} {n : ℕ}
  (comp : steps k (a , w1) ≡ (b , w2))
  → isValue b
  → updCtxt2 name f a
  → compatible· name w1 Res⊤
  → ∀𝕎-get0-NUM w1 name
  → ¬ name ∈ names𝕎· w1
  → name ∈ dom𝕎· w1
  → (getT≤ℕ w2 n name --getT 0 name w2 ≡ just (NUM n)
      → isHighestℕ {k} {w1} {w2} {a} {b} n name comp)
     × ∈names𝕎 {k} {w1} {w2} {a} {b} name comp


stepsPresHighestℕ2 : (name : Name) (f : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
stepsPresHighestℕ2 name f b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    steps k (b , w) ≡ (v , w')
    × isValue v
    × ((k' : ℕ) → k' ≤ k → presHighestℕ2 name f k'))))


ΣhighestUpdCtxtAux2 : (k' : ℕ) (name : Name) (f : Term) (n : ℕ) (a a' : Term) (w0 w w' : 𝕎·) → Set(L)
ΣhighestUpdCtxtAux2 k' name f n a a' w0 w w' =
  Σ (steps k' (a , w) ≡ (a' , w')) (λ comp →
    (getT≤ℕ w' n name → (getT≤ℕ w0 n name × isHighestℕ {k'} {w} {w'} {a} {a'} n name comp))
    × ∈names𝕎 {k'} {w} {w'} {a} {a'} name comp
    × updCtxt2 name f a')


ΣhighestUpdCtxt2 : (name : Name) (f : Term) (n : ℕ) (a : Term) (w0 w : 𝕎·) → Set(L)
ΣhighestUpdCtxt2 name f n a w0 w =
  Σ ℕ (λ k' → Σ Term (λ a' → Σ 𝕎· (λ w' →
    ΣhighestUpdCtxtAux2 k' name f n a a' w0 w w')))


→updCtxt2-shiftUp : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                   → updCtxt2 name f a
                   → updCtxt2 name f (shiftUp v a)
→updCtxt2-shiftUp v {name} {f} cf {.(VAR x)} (updCtxt2-VAR x) = updCtxt2-VAR _
→updCtxt2-shiftUp v {name} {f} cf {.NAT} updCtxt2-NAT = updCtxt2-NAT
→updCtxt2-shiftUp v {name} {f} cf {.QNAT} updCtxt2-QNAT = updCtxt2-QNAT
→updCtxt2-shiftUp v {name} {f} cf {.(LT a b)} (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(QLT a b)} (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(NUM x)} (updCtxt2-NUM x) = updCtxt2-NUM _
→updCtxt2-shiftUp v {name} {f} cf {.(IFLT a b c d)} (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃) (→updCtxt2-shiftUp v cf upd₄)
→updCtxt2-shiftUp v {name} {f} cf {.(SUC a)} (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(PI a b)} (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(LAMBDA a)} (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (→updCtxt2-shiftUp (suc v) cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(APPLY a b)} (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(FIX a)} (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(LET a b)} (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(SUM a b)} (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(PAIR a b)} (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(SPREAD a b)} (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc (suc v)) cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(SET a b)} (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(ISECT a b)} (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(TUNION a b)} (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(UNION a b)} (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(QTUNION a b)} (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(INL a)} (updCtxt2-INL a upd₁) = updCtxt2-INL _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(INR a)} (updCtxt2-INR a upd₁) = updCtxt2-INR _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(DECIDE a b c)} (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂) (→updCtxt2-shiftUp (suc v) cf upd₃)
→updCtxt2-shiftUp v {name} {f} cf {.(EQ a b c)} (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃)
→updCtxt2-shiftUp v {name} {f} cf {.AX} updCtxt2-AX = updCtxt2-AX
→updCtxt2-shiftUp v {name} {f} cf {.FREE} updCtxt2-FREE = updCtxt2-FREE
→updCtxt2-shiftUp v {name} {f} cf {.(CS name')} (updCtxt2-CS name') = updCtxt2-CS _
→updCtxt2-shiftUp v {name} {f} cf {.(NAME name')} (updCtxt2-NAME name' x) = updCtxt2-NAME _ x
→updCtxt2-shiftUp v {name} {f} cf {.(FRESH a)} (updCtxt2-FRESH a upd₁) = updCtxt2-FRESH _ (→updCtxt2-shiftUp v (→#shiftNameUp 0 {f} cf) upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(CHOOSE a b)} (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(TSQUASH a)} (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(TTRUNC a)} (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(TCONST a)} (updCtxt2-TCONST a upd₁) = updCtxt2-TCONST _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(SUBSING a)} (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.PURE} updCtxt2-PURE = updCtxt2-PURE
→updCtxt2-shiftUp v {name} {f} cf {.(DUM a)} (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(FFDEFS a b)} (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
→updCtxt2-shiftUp v {name} {f} cf {.(UNIV x)} (updCtxt2-UNIV x) = updCtxt2-UNIV _
→updCtxt2-shiftUp v {name} {f} cf {.(LIFT a)} (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(LOWER a)} (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(SHRINK a)} (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (→updCtxt2-shiftUp v cf upd₁)
→updCtxt2-shiftUp v {name} {f} cf {.(upd name f)} updCtxt2-upd
  rewrite sucIf≤s0 v | #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updCtxt2-upd


→updCtxt2-shiftDown : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                   → updCtxt2 name f a
                   → updCtxt2 name f (shiftDown v a)
→updCtxt2-shiftDown v {name} {f} cf {.(VAR x)} (updCtxt2-VAR x) = updCtxt2-VAR _
→updCtxt2-shiftDown v {name} {f} cf {.NAT} updCtxt2-NAT = updCtxt2-NAT
→updCtxt2-shiftDown v {name} {f} cf {.QNAT} updCtxt2-QNAT = updCtxt2-QNAT
→updCtxt2-shiftDown v {name} {f} cf {.(LT a b)} (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(QLT a b)} (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(NUM x)} (updCtxt2-NUM x) = updCtxt2-NUM _
→updCtxt2-shiftDown v {name} {f} cf {.(IFLT a b c d)} (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃) (→updCtxt2-shiftDown v cf upd₄)
→updCtxt2-shiftDown v {name} {f} cf {.(SUC a)} (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(PI a b)} (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(LAMBDA a)} (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (→updCtxt2-shiftDown (suc v) cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(APPLY a b)} (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(FIX a)} (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(LET a b)} (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(SUM a b)} (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(PAIR a b)} (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(SPREAD a b)} (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc (suc v)) cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(SET a b)} (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(ISECT a b)} (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(TUNION a b)} (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(UNION a b)} (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(QTUNION a b)} (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(INL a)} (updCtxt2-INL a upd₁) = updCtxt2-INL _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(INR a)} (updCtxt2-INR a upd₁) = updCtxt2-INR _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(DECIDE a b c)} (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂) (→updCtxt2-shiftDown (suc v) cf upd₃)
→updCtxt2-shiftDown v {name} {f} cf {.(EQ a b c)} (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃)
→updCtxt2-shiftDown v {name} {f} cf {.AX} updCtxt2-AX = updCtxt2-AX
→updCtxt2-shiftDown v {name} {f} cf {.FREE} updCtxt2-FREE = updCtxt2-FREE
→updCtxt2-shiftDown v {name} {f} cf {.(CS name')} (updCtxt2-CS name') = updCtxt2-CS _
→updCtxt2-shiftDown v {name} {f} cf {.(NAME name')} (updCtxt2-NAME name' x) = updCtxt2-NAME _ x
→updCtxt2-shiftDown v {name} {f} cf {.(FRESH a)} (updCtxt2-FRESH a upd₁) = updCtxt2-FRESH _ (→updCtxt2-shiftDown v (→#shiftNameUp 0 {f} cf) upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(CHOOSE a b)} (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(TSQUASH a)} (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(TTRUNC a)} (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(TCONST a)} (updCtxt2-TCONST a upd₁) = updCtxt2-TCONST _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(SUBSING a)} (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.PURE} updCtxt2-PURE = updCtxt2-PURE
→updCtxt2-shiftDown v {name} {f} cf {.(DUM a)} (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(FFDEFS a b)} (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
→updCtxt2-shiftDown v {name} {f} cf {.(UNIV x)} (updCtxt2-UNIV x) = updCtxt2-UNIV _
→updCtxt2-shiftDown v {name} {f} cf {.(LIFT a)} (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(LOWER a)} (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(SHRINK a)} (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (→updCtxt2-shiftDown v cf upd₁)
→updCtxt2-shiftDown v {name} {f} cf {.(upd name f)} updCtxt2-upd
  rewrite sucIf≤s0 v | #shiftDown (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updCtxt2-upd


→updCtxt2-shiftNameUp : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                         → updCtxt2 name f a
                         → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a)
→updCtxt2-shiftNameUp v {name} {f} cf {.(VAR x)} (updCtxt2-VAR x) = updCtxt2-VAR _
→updCtxt2-shiftNameUp v {name} {f} cf {.NAT} updCtxt2-NAT = updCtxt2-NAT
→updCtxt2-shiftNameUp v {name} {f} cf {.QNAT} updCtxt2-QNAT = updCtxt2-QNAT
→updCtxt2-shiftNameUp v {name} {f} cf {.(LT a b)} (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(QLT a b)} (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(NUM x)} (updCtxt2-NUM x) = updCtxt2-NUM _
→updCtxt2-shiftNameUp v {name} {f} cf {.(IFLT a b c d)} (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃) (→updCtxt2-shiftNameUp v cf upd₄)
→updCtxt2-shiftNameUp v {name} {f} cf {.(SUC a)} (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(PI a b)} (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(LAMBDA a)} (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(APPLY a b)} (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(FIX a)} (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(LET a b)} (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(SUM a b)} (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(PAIR a b)} (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(SPREAD a b)} (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(SET a b)} (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(ISECT a b)} (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(TUNION a b)} (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(UNION a b)} (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(QTUNION a b)} (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(INL a)} (updCtxt2-INL a upd₁) = updCtxt2-INL _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(INR a)} (updCtxt2-INR a upd₁) = updCtxt2-INR _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(DECIDE a b c)} (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
→updCtxt2-shiftNameUp v {name} {f} cf {.(EQ a b c)} (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
→updCtxt2-shiftNameUp v {name} {f} cf {.AX} updCtxt2-AX = updCtxt2-AX
→updCtxt2-shiftNameUp v {name} {f} cf {.FREE} updCtxt2-FREE = updCtxt2-FREE
→updCtxt2-shiftNameUp v {name} {f} cf {.(CS name')} (updCtxt2-CS name') = updCtxt2-CS _
→updCtxt2-shiftNameUp v {name} {f} cf {.(NAME name')} (updCtxt2-NAME name' x) = updCtxt2-NAME (sucIf≤ v name') (λ y → x (sucIf≤-inj y))
→updCtxt2-shiftNameUp v {name} {f} cf {.(FRESH a)} (updCtxt2-FRESH a upd₁) =
  updCtxt2-FRESH (shiftNameUp (suc v) a) c1
  where
    c3 : updCtxt2 (sucIf≤ (suc v) (suc name))
                (shiftNameUp (suc v) (shiftNameUp 0 f))
                (shiftNameUp (suc v) a)
    c3 = →updCtxt2-shiftNameUp (suc v) {suc name} (→#shiftNameUp 0 {f} cf) upd₁

    c2 : updCtxt2 (suc (sucIf≤ v name))
                (shiftNameUp (suc v) (shiftNameUp 0 f))
                (shiftNameUp (suc v) a)
    c2 rewrite suc-sucIf≤ v name = c3

    c1 : updCtxt2 (suc (sucIf≤ v name))
                (shiftNameUp 0 (shiftNameUp v f))
                (shiftNameUp (suc v) a)
    c1 rewrite shiftNameUp-shiftNameUp {0} {v} {f} _≤_.z≤n = c2
→updCtxt2-shiftNameUp v {name} {f} cf {.(CHOOSE a b)} (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(TSQUASH a)} (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(TTRUNC a)} (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(TCONST a)} (updCtxt2-TCONST a upd₁) = updCtxt2-TCONST _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(SUBSING a)} (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.PURE} updCtxt2-PURE = updCtxt2-PURE
→updCtxt2-shiftNameUp v {name} {f} cf {.(DUM a)} (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(FFDEFS a b)} (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
→updCtxt2-shiftNameUp v {name} {f} cf {.(UNIV x)} (updCtxt2-UNIV x) = updCtxt2-UNIV _
→updCtxt2-shiftNameUp v {name} {f} cf {.(LIFT a)} (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(LOWER a)} (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(SHRINK a)} (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (→updCtxt2-shiftNameUp v cf upd₁)
→updCtxt2-shiftNameUp v {name} {f} cf {.(upd name f)} updCtxt2-upd = c2
  where
    c1 : updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (upd (sucIf≤ v name) (shiftNameUp v f))
    c1 = updCtxt2-upd

    c2 : updCtxt2 (sucIf≤ v name) (shiftNameUp v f)
                  (LAMBDA (LET (VAR 0)
                               (LET (IFLT (APPLY (CS (sucIf≤ v name)) (NUM 0)) (VAR 0)
                                          (CHOOSE (NAME (sucIf≤ v name)) (VAR 0)) AX)
                                    (APPLY (shiftNameUp v (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
    c2 rewrite sym (shiftUp-shiftNameUp 0 v f)  = c1



→updCtxt2-shiftNameUp0 : {name : Name} {f : Term} (cf : # f) {a : Term}
                   → updCtxt2 name f a
                   → updCtxt2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 a)
→updCtxt2-shiftNameUp0 {name} {f} cf {a} dif
  rewrite suc≡sucIf≤0 name =
  →updCtxt2-shiftNameUp 0 {name} cf dif



updCtxt2-subv : {name : Name} {f : Term} (cf : # f) (v : Var) {a b : Term}
             → updCtxt2 name f a
             → updCtxt2 name f b
             → updCtxt2 name f (subv v b a)
updCtxt2-subv {name} {f} cf v {.(VAR x)} {b} (updCtxt2-VAR x) updb with x ≟ v
... | yes p = updb
... | no p = updCtxt2-VAR _
updCtxt2-subv {name} {f} cf v {.NAT} {b} updCtxt2-NAT updb = updCtxt2-NAT
updCtxt2-subv {name} {f} cf v {.QNAT} {b} updCtxt2-QNAT updb = updCtxt2-QNAT
updCtxt2-subv {name} {f} cf v {.(LT a b₁)} {b} (updCtxt2-LT a b₁ upda upda₁) updb = updCtxt2-LT _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(QLT a b₁)} {b} (updCtxt2-QLT a b₁ upda upda₁) updb = updCtxt2-QLT _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(NUM x)} {b} (updCtxt2-NUM x) updb = updCtxt2-NUM _
updCtxt2-subv {name} {f} cf v {.(IFLT a b₁ c d)} {b} (updCtxt2-IFLT a b₁ c d upda upda₁ upda₂ upda₃) updb = updCtxt2-IFLT _ _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb) (updCtxt2-subv cf v upda₃ updb)
updCtxt2-subv {name} {f} cf v {.(SUC a)} {b} (updCtxt2-SUC a upda) updb = updCtxt2-SUC _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(PI a b₁)} {b} (updCtxt2-PI a b₁ upda upda₁) updb = updCtxt2-PI _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(LAMBDA a)} {b} (updCtxt2-LAMBDA a upda) updb = updCtxt2-LAMBDA _ (updCtxt2-subv cf (suc v) upda (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(APPLY a b₁)} {b} (updCtxt2-APPLY a b₁ upda upda₁) updb = updCtxt2-APPLY _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(FIX a)} {b} (updCtxt2-FIX a upda) updb = updCtxt2-FIX _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(LET a b₁)} {b} (updCtxt2-LET a b₁ upda upda₁) updb = updCtxt2-LET _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(SUM a b₁)} {b} (updCtxt2-SUM a b₁ upda upda₁) updb = updCtxt2-SUM _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(PAIR a b₁)} {b} (updCtxt2-PAIR a b₁ upda upda₁) updb = updCtxt2-PAIR _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(SPREAD a b₁)} {b} (updCtxt2-SPREAD a b₁ upda upda₁) updb = updCtxt2-SPREAD _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc (suc v)) upda₁ (→updCtxt2-shiftUp 0 cf (→updCtxt2-shiftUp 0 cf updb)))
updCtxt2-subv {name} {f} cf v {.(SET a b₁)} {b} (updCtxt2-SET a b₁ upda upda₁) updb = updCtxt2-SET _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(ISECT a b₁)} {b} (updCtxt2-ISECT a b₁ upda upda₁) updb = updCtxt2-ISECT _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(TUNION a b₁)} {b} (updCtxt2-TUNION a b₁ upda upda₁) updb = updCtxt2-TUNION _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(UNION a b₁)} {b} (updCtxt2-UNION a b₁ upda upda₁) updb = updCtxt2-UNION _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(QTUNION a b₁)} {b} (updCtxt2-QTUNION a b₁ upda upda₁) updb = updCtxt2-QTUNION _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(INL a)} {b} (updCtxt2-INL a upda) updb = updCtxt2-INL _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(INR a)} {b} (updCtxt2-INR a upda) updb = updCtxt2-INR _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(DECIDE a b₁ c)} {b} (updCtxt2-DECIDE a b₁ c upda upda₁ upda₂) updb = updCtxt2-DECIDE _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb)) (updCtxt2-subv cf (suc v) upda₂ (→updCtxt2-shiftUp 0 cf updb))
updCtxt2-subv {name} {f} cf v {.(EQ a b₁ c)} {b} (updCtxt2-EQ a b₁ c upda upda₁ upda₂) updb = updCtxt2-EQ _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb)
updCtxt2-subv {name} {f} cf v {.AX} {b} updCtxt2-AX updb = updCtxt2-AX
updCtxt2-subv {name} {f} cf v {.FREE} {b} updCtxt2-FREE updb = updCtxt2-FREE
updCtxt2-subv {name} {f} cf v {.(CS name')} {b} (updCtxt2-CS name') updb = updCtxt2-CS _
updCtxt2-subv {name} {f} cf v {.(NAME name')} {b} (updCtxt2-NAME name' x) updb = updCtxt2-NAME _ x
updCtxt2-subv {name} {f} cf v {.(FRESH a)} {b} (updCtxt2-FRESH a upda) updb = updCtxt2-FRESH _ (updCtxt2-subv (→#shiftNameUp 0 {f} cf) v upda (→updCtxt2-shiftNameUp0 {name} cf updb))
updCtxt2-subv {name} {f} cf v {.(CHOOSE a b₁)} {b} (updCtxt2-CHOOSE a b₁ upda upda₁) updb = updCtxt2-CHOOSE _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(TSQUASH a)} {b} (updCtxt2-TSQUASH a upda) updb = updCtxt2-TSQUASH _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(TTRUNC a)} {b} (updCtxt2-TTRUNC a upda) updb = updCtxt2-TTRUNC _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(TCONST a)} {b} (updCtxt2-TCONST a upda) updb = updCtxt2-TCONST _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(SUBSING a)} {b} (updCtxt2-SUBSING a upda) updb = updCtxt2-SUBSING _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.PURE} {b} updCtxt2-PURE updb = updCtxt2-PURE
updCtxt2-subv {name} {f} cf v {.(DUM a)} {b} (updCtxt2-DUM a upda) updb = updCtxt2-DUM _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(FFDEFS a b₁)} {b} (updCtxt2-FFDEFS a b₁ upda upda₁) updb = updCtxt2-FFDEFS _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
updCtxt2-subv {name} {f} cf v {.(UNIV x)} {b} (updCtxt2-UNIV x) updb = updCtxt2-UNIV _
updCtxt2-subv {name} {f} cf v {.(LIFT a)} {b} (updCtxt2-LIFT a upda) updb = updCtxt2-LIFT _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(LOWER a)} {b} (updCtxt2-LOWER a upda) updb = updCtxt2-LOWER _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(SHRINK a)} {b} (updCtxt2-SHRINK a upda) updb = updCtxt2-SHRINK _ (updCtxt2-subv cf v upda updb)
updCtxt2-subv {name} {f} cf v {.(upd name f)} {b} updCtxt2-upd updb
  rewrite sucIf≤00
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
  = updCtxt2-upd



updCtxt2-sub : {name : Name} {f : Term} (cf : # f) {a b : Term}
             → updCtxt2 name f a
             → updCtxt2 name f b
             → updCtxt2 name f (sub b a)
updCtxt2-sub {name} {f} cf {a} {b} d₁ d₂ =
  →updCtxt2-shiftDown 0 cf (updCtxt2-subv {name} {f} cf 0 {a} {shiftUp 0 b} d₁ (→updCtxt2-shiftUp 0 cf d₂))


updCtxt2-LAMBDA→ : {name : Name} {f t : Term}
                   → updCtxt2 name f (LAMBDA t)
                   → updCtxt2 name f t ⊎ t ≡ updBody name f
updCtxt2-LAMBDA→ {name} {f} {t} (updCtxt2-LAMBDA .t u) = inj₁ u
updCtxt2-LAMBDA→ {name} {f} {.(updBody name f)} updCtxt2-upd = inj₂ refl



updCtxt2-NAME→ : {name name' : Name} {f : Term}
                   → updCtxt2 name f (NAME name')
                   → ¬ name' ≡ name
updCtxt2-NAME→ {name} {name'} {f} (updCtxt2-NAME .name' x) = x



updCtxt2-PAIR→₁ : {name : Name} {f a b : Term}
                   → updCtxt2 name f (PAIR a b)
                   → updCtxt2 name f a
updCtxt2-PAIR→₁ {name} {f} {a} {b} (updCtxt2-PAIR .a .b ca cb) = ca



updCtxt2-PAIR→₂ : {name : Name} {f a b : Term}
                   → updCtxt2 name f (PAIR a b)
                   → updCtxt2 name f b
updCtxt2-PAIR→₂ {name} {f} {a} {b} (updCtxt2-PAIR .a .b ca cb) = cb



updCtxt2-INL→ : {name : Name} {f a : Term}
                   → updCtxt2 name f (INL a)
                   → updCtxt2 name f a
updCtxt2-INL→ {name} {f} {a} (updCtxt2-INL .a ca) = ca



updCtxt2-INR→ : {name : Name} {f a : Term}
                   → updCtxt2 name f (INR a)
                   → updCtxt2 name f a
updCtxt2-INR→ {name} {f} {a} (updCtxt2-INR .a ca) = ca



¬∈++2→¬∈1 : {L : Level} {A : Set(L)} {a b : List A} {x : A}
             → ¬ x ∈ (a ++ b)
             → ¬ x ∈ a
¬∈++2→¬∈1 {L} {A} {a} {b} {x} ni i = ni (∈-++⁺ˡ i)



¬∈++2→¬∈2 : {L : Level} {A : Set(L)} {a b : List A} {x : A}
             → ¬ x ∈ (a ++ b)
             → ¬ x ∈ b
¬∈++2→¬∈2 {L} {A} {a} {b} {x} ni i = ni (∈-++⁺ʳ a i)


¬∈++3→¬∈1 : {L : Level} {A : Set(L)} {a b c : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c)
             → ¬ x ∈ a
¬∈++3→¬∈1 {L} {A} {a} {b} {c} {x} ni i = ni (∈-++⁺ˡ i)


¬∈++3→¬∈2 : {L : Level} {A : Set(L)} {a b c : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c)
             → ¬ x ∈ b
¬∈++3→¬∈2 {L} {A} {a} {b} {c} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ˡ i))


¬∈++3→¬∈3 : {L : Level} {A : Set(L)} {a b c : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c)
             → ¬ x ∈ c
¬∈++3→¬∈3 {L} {A} {a} {b} {c} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ʳ b i))



¬∈++4→¬∈1 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ a
¬∈++4→¬∈1 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ˡ i)


¬∈++4→¬∈2 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ b
¬∈++4→¬∈2 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ˡ i))


¬∈++4→¬∈3 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ c
¬∈++4→¬∈3 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ˡ i)))


¬∈++4→¬∈4 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ d
¬∈++4→¬∈4 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ʳ c i)))


¬∈names-APPLY : {name : Name} {a b : Term}
                → ¬ name ∈ names a
                → ¬ name ∈ names b
                → ¬ name ∈ names (APPLY a b)
¬∈names-APPLY {name} {a} {b} na nb i with ∈-++⁻ (names a) i
... | inj₁ p = na p
... | inj₂ p = nb p


¬∈names-NUM : {name : Name} {n : ℕ}
               → ¬ name ∈ names (NUM n)
¬∈names-NUM {name} {n} ()


updCtxt2-refl : (name : Name) (f t : Term)
                → ¬ name ∈ names t
                → updCtxt2 name f t
updCtxt2-refl name f (VAR x) nn = updCtxt2-VAR _
updCtxt2-refl name f NAT nn = updCtxt2-NAT
updCtxt2-refl name f QNAT nn = updCtxt2-QNAT
updCtxt2-refl name f (LT t t₁) nn = updCtxt2-LT _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (QLT t t₁) nn = updCtxt2-QLT _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (NUM x) nn = updCtxt2-NUM _
updCtxt2-refl name f (IFLT t t₁ t₂ t₃) nn = updCtxt2-IFLT _ _ _ _ (updCtxt2-refl name f t (¬∈++4→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₁ (¬∈++4→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₂ (¬∈++4→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₃ (¬∈++4→¬∈4 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn))
updCtxt2-refl name f (SUC t) nn = updCtxt2-SUC _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (PI t t₁) nn = updCtxt2-PI _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (LAMBDA t) nn = updCtxt2-LAMBDA _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (APPLY t t₁) nn = updCtxt2-APPLY _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (FIX t) nn = updCtxt2-FIX _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (LET t t₁) nn = updCtxt2-LET _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (SUM t t₁) nn = updCtxt2-SUM _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (PAIR t t₁) nn = updCtxt2-PAIR _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (SPREAD t t₁) nn = updCtxt2-SPREAD _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (SET t t₁) nn = updCtxt2-SET _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (TUNION t t₁) nn = updCtxt2-TUNION _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (ISECT t t₁) nn = updCtxt2-ISECT _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (UNION t t₁) nn = updCtxt2-UNION _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (QTUNION t t₁) nn = updCtxt2-QTUNION _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (INL t) nn = updCtxt2-INL _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (INR t) nn = updCtxt2-INR _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (DECIDE t t₁ t₂) nn = updCtxt2-DECIDE _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
updCtxt2-refl name f (EQ t t₁ t₂) nn = updCtxt2-EQ _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
updCtxt2-refl name f AX nn = updCtxt2-AX
updCtxt2-refl name f FREE nn = updCtxt2-FREE
updCtxt2-refl name f (CS x) nn = updCtxt2-CS _
updCtxt2-refl name f (NAME x) nn = updCtxt2-NAME x (λ z → nn (here (sym z)))
updCtxt2-refl name f (FRESH t) nn = updCtxt2-FRESH t (updCtxt2-refl (suc name) (shiftNameUp 0 f) t (λ z → nn (suc→∈lowerNames {name} {names t} z)))
updCtxt2-refl name f (CHOOSE t t₁) nn = updCtxt2-CHOOSE _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f (TSQUASH t) nn = updCtxt2-TSQUASH _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (TTRUNC t) nn = updCtxt2-TTRUNC _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (TCONST t) nn = updCtxt2-TCONST _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (SUBSING t) nn = updCtxt2-SUBSING _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (DUM t) nn = updCtxt2-DUM _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (FFDEFS t t₁) nn = updCtxt2-FFDEFS _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
updCtxt2-refl name f PURE nn = updCtxt2-PURE
updCtxt2-refl name f (UNIV x) nn = updCtxt2-UNIV _
updCtxt2-refl name f (LIFT t) nn = updCtxt2-LIFT _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (LOWER t) nn = updCtxt2-LOWER _ (updCtxt2-refl name f t nn)
updCtxt2-refl name f (SHRINK t) nn = updCtxt2-SHRINK _ (updCtxt2-refl name f t nn)



→≡sucIf≤ : {v : Var} {a b : Var}
            → a ≡ b
            → sucIf≤ v a ≡ sucIf≤ v b
→≡sucIf≤ {v} {a} {b} e rewrite e = refl


NAMEinj : {n m : Name} → NAME n ≡ NAME m → n ≡ m
NAMEinj refl =  refl


shiftNameUp-inj : {n : Name} {a b : Term} → shiftNameUp n a ≡ shiftNameUp n b → a ≡ b
shiftNameUp-inj {n} {VAR x} {VAR x} refl = refl
shiftNameUp-inj {n} {NAT} {NAT} e = refl
shiftNameUp-inj {n} {QNAT} {QNAT} e = refl
shiftNameUp-inj {n} {LT a a₁} {LT b b₁} e rewrite shiftNameUp-inj (LTinj1 e) | shiftNameUp-inj (LTinj2 e) = refl
shiftNameUp-inj {n} {QLT a a₁} {QLT b b₁} e rewrite shiftNameUp-inj (QLTinj1 e) | shiftNameUp-inj (QLTinj2 e) = refl
shiftNameUp-inj {n} {NUM x} {NUM .x} refl = refl
shiftNameUp-inj {n} {IFLT a a₁ a₂ a₃} {IFLT b b₁ b₂ b₃} e rewrite shiftNameUp-inj (IFLTinj1 e) | shiftNameUp-inj (IFLTinj2 e) | shiftNameUp-inj (IFLTinj3 e) | shiftNameUp-inj (IFLTinj4 e) = refl
shiftNameUp-inj {n} {SUC a} {SUC b} e rewrite shiftNameUp-inj (SUCinj e) = refl
shiftNameUp-inj {n} {PI a a₁} {PI b b₁} e rewrite shiftNameUp-inj (PIinj1 e) | shiftNameUp-inj (PIinj2 e) = refl
shiftNameUp-inj {n} {LAMBDA a} {LAMBDA b} e rewrite shiftNameUp-inj (LAMinj e) = refl
shiftNameUp-inj {n} {APPLY a a₁} {APPLY b b₁} e rewrite shiftNameUp-inj (APPLYinj1 e) | shiftNameUp-inj (APPLYinj2 e) = refl
shiftNameUp-inj {n} {FIX a} {FIX b} e rewrite shiftNameUp-inj (FIXinj e) = refl
shiftNameUp-inj {n} {LET a a₁} {LET b b₁} e rewrite shiftNameUp-inj (LETinj1 e) | shiftNameUp-inj (LETinj2 e) = refl
shiftNameUp-inj {n} {SUM a a₁} {SUM b b₁} e rewrite shiftNameUp-inj (SUMinj1 e) | shiftNameUp-inj (SUMinj2 e) = refl
shiftNameUp-inj {n} {PAIR a a₁} {PAIR b b₁} e rewrite shiftNameUp-inj (PAIRinj1 e) | shiftNameUp-inj (PAIRinj2 e) = refl
shiftNameUp-inj {n} {SPREAD a a₁} {SPREAD b b₁} e rewrite shiftNameUp-inj (SPREADinj1 e) | shiftNameUp-inj (SPREADinj2 e) = refl
shiftNameUp-inj {n} {SET a a₁} {SET b b₁} e rewrite shiftNameUp-inj (SETinj1 e) | shiftNameUp-inj (SETinj2 e) = refl
shiftNameUp-inj {n} {ISECT a a₁} {ISECT b b₁} e rewrite shiftNameUp-inj (ISECTinj1 e) | shiftNameUp-inj (ISECTinj2 e) = refl
shiftNameUp-inj {n} {TUNION a a₁} {TUNION b b₁} e rewrite shiftNameUp-inj (TUNIONinj1 e) | shiftNameUp-inj (TUNIONinj2 e) = refl
shiftNameUp-inj {n} {UNION a a₁} {UNION b b₁} e rewrite shiftNameUp-inj (UNIONinj1 e) | shiftNameUp-inj (UNIONinj2 e) = refl
shiftNameUp-inj {n} {QTUNION a a₁} {QTUNION b b₁} e rewrite shiftNameUp-inj (QTUNIONinj1 e) | shiftNameUp-inj (QTUNIONinj2 e) = refl
shiftNameUp-inj {n} {INL a} {INL b} e rewrite shiftNameUp-inj (INLinj e) = refl
shiftNameUp-inj {n} {INR a} {INR b} e rewrite shiftNameUp-inj (INRinj e) = refl
shiftNameUp-inj {n} {DECIDE a a₁ a₂} {DECIDE b b₁ b₂} e rewrite shiftNameUp-inj (DECIDEinj1 e) | shiftNameUp-inj (DECIDEinj2 e) | shiftNameUp-inj (DECIDEinj3 e) = refl
shiftNameUp-inj {n} {EQ a a₁ a₂} {EQ b b₁ b₂} e rewrite shiftNameUp-inj (EQinj1 e) | shiftNameUp-inj (EQinj2 e) | shiftNameUp-inj (EQinj3 e) = refl
shiftNameUp-inj {n} {AX} {AX} e = refl
shiftNameUp-inj {n} {FREE} {FREE} e = refl
shiftNameUp-inj {n} {CS x} {CS x₁} e = ≡CS (sucIf≤-inj {n} {x} {x₁} (CSinj e))
shiftNameUp-inj {n} {NAME x} {NAME x₁} e = ≡NAME (sucIf≤-inj {n} {x} {x₁} (NAMEinj e))
shiftNameUp-inj {n} {FRESH a} {FRESH b} e rewrite shiftNameUp-inj (FRESHinj e) = refl
shiftNameUp-inj {n} {CHOOSE a a₁} {CHOOSE b b₁} e rewrite shiftNameUp-inj (CHOOSEinj1 e) | shiftNameUp-inj (CHOOSEinj2 e) = refl
--shiftNameUp-inj {n} {IFC0 a a₁ a₂} {IFC0 b b₁ b₂} e rewrite shiftNameUp-inj (IFC0inj1 e) | shiftNameUp-inj (IFC0inj2 e) | shiftNameUp-inj (IFC0inj3 e) = refl
shiftNameUp-inj {n} {TSQUASH a} {TSQUASH b} e rewrite shiftNameUp-inj (TSQUASHinj e) = refl
shiftNameUp-inj {n} {TTRUNC a} {TTRUNC b} e rewrite shiftNameUp-inj (TTRUNCinj e) = refl
shiftNameUp-inj {n} {TCONST a} {TCONST b} e rewrite shiftNameUp-inj (TCONSTinj e) = refl
shiftNameUp-inj {n} {SUBSING a} {SUBSING b} e rewrite shiftNameUp-inj (SUBSINGinj e) = refl
shiftNameUp-inj {n} {DUM a} {DUM b} e rewrite shiftNameUp-inj (DUMinj e) = refl
shiftNameUp-inj {n} {FFDEFS a a₁} {FFDEFS b b₁} e rewrite shiftNameUp-inj (FFDEFSinj1 e) | shiftNameUp-inj (FFDEFSinj2 e) = refl
shiftNameUp-inj {n} {PURE} {PURE} refl = refl
shiftNameUp-inj {n} {UNIV x} {UNIV .x} refl = refl
shiftNameUp-inj {n} {LIFT a} {LIFT b} e rewrite shiftNameUp-inj (LIFTinj e) = refl
shiftNameUp-inj {n} {LOWER a} {LOWER b} e rewrite shiftNameUp-inj (LOWERinj e) = refl
shiftNameUp-inj {n} {SHRINK a} {SHRINK b} e rewrite shiftNameUp-inj (SHRINKinj e) = refl


shiftUp-ShiftNameUp≡ShiftNameUp→ : (v : Name) (f a : Term)
                                    → shiftUp 0 (shiftNameUp v f) ≡ shiftNameUp v a
                                    → a ≡ shiftUp 0 f
shiftUp-ShiftNameUp≡ShiftNameUp→ v f a e
  rewrite shiftUp-shiftNameUp 0 v f = sym (shiftNameUp-inj e)


updBody≡shiftNameUp→ : (v : Var) (name : Name) (f : Term) (a : Term)
                        → updBody (sucIf≤ v name) (shiftNameUp v f) ≡ shiftNameUp v a
                        → a ≡ updBody name f
updBody≡shiftNameUp→ v name f (LET (VAR 0) (LET (IFLT (APPLY (CS x₁) (NUM 0)) (VAR 0) (CHOOSE (NAME x₂) (VAR 0)) AX) (APPLY a (VAR 1)))) e
  rewrite sym (sucIf≤-inj {v} {name} {x₁} (CSinj (APPLYinj1 (IFLTinj1 (LETinj1 (LETinj2 e))))))
        | sym (sucIf≤-inj {v} {name} {x₂} (NAMEinj (CHOOSEinj1 (IFLTinj3 (LETinj1 (LETinj2 e))))))
        | shiftUp-ShiftNameUp≡ShiftNameUp→ v f a (APPLYinj1 (LETinj2 (LETinj2 e))) = refl



updCtxt2-shiftNameUp-LAMBDA→ : (v : Var) {name : Name} {f : Term} (cf : # f) {a t : Term}
                                → t ≡ shiftNameUp v a
                                → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (LAMBDA t)
                                → (updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a) → updCtxt2 name f a)
                                → updCtxt2 name f (LAMBDA a)
updCtxt2-shiftNameUp-LAMBDA→ v {name} {f} cf {a} {t} e (updCtxt2-LAMBDA .t upd₁) ind rewrite e = updCtxt2-LAMBDA _ (ind upd₁)
updCtxt2-shiftNameUp-LAMBDA→ v {name} {f} cf {a} {.(updBody (sucIf≤ v name) (shiftNameUp v f))} e updCtxt2-upd ind
  rewrite updBody≡shiftNameUp→ v name f a e = updCtxt2-upd



updCtxt2-shiftNameUp→ : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                         → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a)
                         → updCtxt2 name f a
updCtxt2-shiftNameUp→ v {name} {f} cf {VAR x} (updCtxt2-VAR .x) = updCtxt2-VAR _
updCtxt2-shiftNameUp→ v {name} {f} cf {NAT} upd = updCtxt2-NAT
updCtxt2-shiftNameUp→ v {name} {f} cf {QNAT} upd = updCtxt2-QNAT
updCtxt2-shiftNameUp→ v {name} {f} cf {LT a a₁} (updCtxt2-LT .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-LT _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {QLT a a₁} (updCtxt2-QLT .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-QLT _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {NUM x} upd = updCtxt2-NUM _
updCtxt2-shiftNameUp→ v {name} {f} cf {IFLT a a₁ a₂ a₃} (updCtxt2-IFLT .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) .(shiftNameUp v a₃) upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃) (updCtxt2-shiftNameUp→ v cf upd₄)
updCtxt2-shiftNameUp→ v {name} {f} cf {SUC a} (updCtxt2-SUC .(shiftNameUp v a) upd₁) = updCtxt2-SUC _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {PI a a₁} (updCtxt2-PI .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-PI _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {LAMBDA a} upd =
  updCtxt2-shiftNameUp-LAMBDA→ v {name} {f} cf {a} {shiftNameUp v a} refl upd ind
  where
    ind : updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a) → updCtxt2 name f a
    ind = updCtxt2-shiftNameUp→ v cf
updCtxt2-shiftNameUp→ v {name} {f} cf {APPLY a a₁} (updCtxt2-APPLY .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-APPLY _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {FIX a} (updCtxt2-FIX .(shiftNameUp v a) upd₁) = updCtxt2-FIX _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {LET a a₁} (updCtxt2-LET .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-LET _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {SUM a a₁} (updCtxt2-SUM .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SUM _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {PAIR a a₁} (updCtxt2-PAIR .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-PAIR _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {SPREAD a a₁} (updCtxt2-SPREAD .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SPREAD _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {SET a a₁} (updCtxt2-SET .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SET _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {TUNION a a₁} (updCtxt2-TUNION .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-TUNION _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {ISECT a a₁} (updCtxt2-ISECT .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-ISECT _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {UNION a a₁} (updCtxt2-UNION .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-UNION _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {QTUNION a a₁} (updCtxt2-QTUNION .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-QTUNION _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {INL a} (updCtxt2-INL .(shiftNameUp v a) upd₁) = updCtxt2-INL _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {INR a} (updCtxt2-INR .(shiftNameUp v a) upd₁) = updCtxt2-INR _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {DECIDE a a₁ a₂} (updCtxt2-DECIDE .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
updCtxt2-shiftNameUp→ v {name} {f} cf {EQ a a₁ a₂} (updCtxt2-EQ .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
updCtxt2-shiftNameUp→ v {name} {f} cf {AX} upd = updCtxt2-AX
updCtxt2-shiftNameUp→ v {name} {f} cf {FREE} upd = updCtxt2-FREE
updCtxt2-shiftNameUp→ v {name} {f} cf {CS x} upd = updCtxt2-CS _
updCtxt2-shiftNameUp→ v {name} {f} cf {NAME x} (updCtxt2-NAME .(sucIf≤ v x) d) = updCtxt2-NAME _ λ z → d (→≡sucIf≤ z)
updCtxt2-shiftNameUp→ v {name} {f} cf {FRESH a} (updCtxt2-FRESH .(shiftNameUp (suc v) a) upd₁) =
  updCtxt2-FRESH a (updCtxt2-shiftNameUp→ (suc v) {suc name} {shiftNameUp 0 f} (→#shiftNameUp 0 {f} cf) upd1)
  where
    seq : suc (sucIf≤ v name) ≡ sucIf≤ (suc v) (sucIf≤ 0 name)
    seq rewrite sym (sucIf≤-sucIf≤ {name} {0} {v} _≤_.z≤n) | sym (suc≡sucIf≤0 (sucIf≤ v name)) = refl

    upd1 : updCtxt2 (sucIf≤ (suc v) (suc name)) (shiftNameUp (suc v) (shiftNameUp 0 f)) (shiftNameUp (suc v) a)
    upd1 rewrite suc≡sucIf≤0 name | sym seq | sym (shiftNameUp-shiftNameUp {0} {v} {f} _≤_.z≤n) = upd₁
updCtxt2-shiftNameUp→ v {name} {f} cf {CHOOSE a a₁} (updCtxt2-CHOOSE .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-CHOOSE _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {TSQUASH a} (updCtxt2-TSQUASH .(shiftNameUp v a) upd₁) = updCtxt2-TSQUASH _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {TTRUNC a} (updCtxt2-TTRUNC .(shiftNameUp v a) upd₁) = updCtxt2-TTRUNC _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {TCONST a} (updCtxt2-TCONST .(shiftNameUp v a) upd₁) = updCtxt2-TCONST _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {SUBSING a} (updCtxt2-SUBSING .(shiftNameUp v a) upd₁) = updCtxt2-SUBSING _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {DUM a} (updCtxt2-DUM .(shiftNameUp v a) upd₁) = updCtxt2-DUM _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {FFDEFS a a₁} (updCtxt2-FFDEFS .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-FFDEFS _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
updCtxt2-shiftNameUp→ v {name} {f} cf {PURE} upd = updCtxt2-PURE
updCtxt2-shiftNameUp→ v {name} {f} cf {UNIV x} upd = updCtxt2-UNIV _
updCtxt2-shiftNameUp→ v {name} {f} cf {LIFT a} (updCtxt2-LIFT .(shiftNameUp v a) upd₁) = updCtxt2-LIFT _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {LOWER a} (updCtxt2-LOWER .(shiftNameUp v a) upd₁) = updCtxt2-LOWER _ (updCtxt2-shiftNameUp→ v cf upd₁)
updCtxt2-shiftNameUp→ v {name} {f} cf {SHRINK a} (updCtxt2-SHRINK .(shiftNameUp v a) upd₁) = updCtxt2-SHRINK _ (updCtxt2-shiftNameUp→ v cf upd₁)



¬∈names→isHighestℕ-step : (cc : ContConds) {t u : Term} {w1 w2 : 𝕎·} {n : ℕ} {name : Name}
                           → ¬ name ∈ names t
                           → ¬ name ∈ names𝕎· w1
                           → name ∈ dom𝕎· w1
                           → getT≤ℕ w1 n name
                           → step t w1 ≡ just (u , w2)
                           → ¬ name ∈ names u
                              × ¬ name ∈ names𝕎· w2
                              × name ∈ dom𝕎· w2
                              × getT≤ℕ w2 n name
¬∈names→isHighestℕ-step cc {t} {u} {w1} {w2} {n} {name} nnt nnw idom gt comp =
  fst (snd h) , fst (snd (snd h)) , snd (snd (snd h)) , gt2
  where
    h : getT 0 name w1 ≡ getT 0 name w2 × ¬ name ∈ names u × ¬ name ∈ names𝕎· w2 × name ∈ dom𝕎· w2
    h = name¬∈→step cc w1 w2 t u name comp nnt nnw idom

    gt2 : getT≤ℕ w2 n name
    gt2 rewrite (sym (fst h)) = gt


¬∈names→isHighestℕ : (cc : ContConds) {k : ℕ} {t u : Term} {w1 w2 : 𝕎·} {n : ℕ} {name : Name}
                      → ¬ name ∈ names t
                      → ¬ name ∈ names𝕎· w1
                      → name ∈ dom𝕎· w1
                      → getT≤ℕ w1 n name
                      → (comp : steps k (t , w1) ≡ (u , w2))
                      → isHighestℕ {k} {w1} {w2} n name comp
¬∈names→isHighestℕ cc {0} {t} {u} {w1} {w2} {n} {name} nnt nnw idom gtn comp
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = gtn
¬∈names→isHighestℕ cc {suc k} {t} {u} {w1} {w2} {n} {name} nnt nnw idom gtn comp with step⊎ t w1
... | inj₁ (t' , w1' , z) rewrite z =
  gtn , ¬∈names→isHighestℕ cc {k} {t'} {u} {w1'} {w2} {n} {name} (fst q) (fst (snd q)) (fst (snd (snd q))) (snd (snd (snd q))) comp
  where
    q : ¬ name ∈ names t' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1' × getT≤ℕ w1' n name
    q = ¬∈names→isHighestℕ-step cc {t} {t'} {w1} {w1'} {n} {name} nnt nnw idom gtn z
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = gtn



¬∈names→∈names𝕎 : (cc : ContConds) {k : ℕ} {t u : Term} {w1 w2 : 𝕎·} {name : Name}
                      → ¬ name ∈ names t
                      → ¬ name ∈ names𝕎· w1
                      → name ∈ dom𝕎· w1
                      → (comp : steps k (t , w1) ≡ (u , w2))
                      → ∈names𝕎 {k} {w1} {w2} name comp
¬∈names→∈names𝕎 cc {0} {t} {u} {w1} {w2} {name} nnt nnw idom comp
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = nnw , idom
¬∈names→∈names𝕎 cc {suc k} {t} {u} {w1} {w2} {name} nnt nnw idom comp with step⊎ t w1
... | inj₁ (t' , w1' , z) rewrite z =
  nnw , idom ,
  ¬∈names→∈names𝕎 cc {k} {t'} {u} {w1'} {w2} {name} (fst (snd q)) (fst (snd (snd q))) (snd (snd (snd q))) comp
  where
    q : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names t' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
    q = name¬∈→step cc w1 w1' t t' name z nnt nnw idom
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = nnw , idom



→isHighestℕ-upd-body2-NUM3b :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → compatible· name w Res⊤
    → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , chooseT name w (NUM m))
               ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
    → getT 0 name w ≡ just (NUM m')
    → m < n
    → isHighestℕ {k} {chooseT name w (NUM m)} {chooseT name w (NUM m)} n name comp
→isHighestℕ-upd-body2-NUM3b cc gc {0} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat () g0 ltn
→isHighestℕ-upd-body2-NUM3b cc gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 ltn
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftUp 0 (ct f cf) | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  g1 ,
  ¬∈names→isHighestℕ cc {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {chooseT name w (NUM m)} {chooseT name w (NUM m)} {n} {name} (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m})) (λ z → nnw (ContConds.ccNchoose cc name name w (NUM m) (¬∈names-NUM {name} {m}) z)) (ContConds.ccDchoose cc name name w (NUM m) idom) g1 comp
  where
    g1 : getT≤ℕ (chooseT name w (NUM m)) n name
    g1 rewrite gc name w m compat = m , refl , ltn



→isHighestℕ-upd-body2-NUM3b-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , chooseT name w (NUM m))
               ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
    → ∈names𝕎 {k} {chooseT name w (NUM m)} {chooseT name w (NUM m)} name comp
→isHighestℕ-upd-body2-NUM3b-∈names𝕎 cc gc {0} {name} {w} {f} {m} {m'} cf nnf nnw idom comp =
  (λ z → nnw (ContConds.ccNchoose cc name name w (NUM m) (¬∈names-NUM {name} {m}) z)) ,
  ContConds.ccDchoose cc name name w (NUM m) idom
→isHighestℕ-upd-body2-NUM3b-∈names𝕎 cc gc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftUp 0 (ct f cf) | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  (λ z → nnw (ContConds.ccNchoose cc name name w (NUM m) (¬∈names-NUM {name} {m}) z)) ,
  ContConds.ccDchoose cc name name w (NUM m) idom ,
  ¬∈names→∈names𝕎
    cc {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {chooseT name w (NUM m)} {chooseT name w (NUM m)} {name}
    (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
    (λ z → nnw (ContConds.ccNchoose cc name name w (NUM m) (¬∈names-NUM {name} {m}) z))
    (ContConds.ccDchoose cc name name w (NUM m) idom)
    comp



→isHighestℕ-upd-body2-NUM3 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → compatible· name w Res⊤
    → (comp : steps k (LET (CHOOSE (NAME name) (NUM m)) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
    → getT 0 name w ≡ just (NUM m')
    → m' < n
    → m < n
    → isHighestℕ {k} {w} {chooseT name w (NUM m)} n name comp
→isHighestℕ-upd-body2-NUM3 cc gc {0} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat () g0 ltn ltn'
→isHighestℕ-upd-body2-NUM3 cc gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 ltn ltn' =
  (m' , g0 , ltn) ,
  →isHighestℕ-upd-body2-NUM3b cc gc {k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 ltn'





→isHighestℕ-upd-body2-NUM3-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET (CHOOSE (NAME name) (NUM m)) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , chooseT name w (NUM m)))
    → ∈names𝕎 {k} {w} {chooseT name w (NUM m)} name comp
→isHighestℕ-upd-body2-NUM3-∈names𝕎 cc gc {0} {name} {w} {f} {m} {m'} cf nnf nnw idom ()
→isHighestℕ-upd-body2-NUM3-∈names𝕎 cc gc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp =
  nnw , idom ,
  →isHighestℕ-upd-body2-NUM3b-∈names𝕎 cc gc {k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp



→isHighestℕ-upd-body2-NUM4 :
    (cc : ContConds) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , w))
    → getT 0 name w ≡ just (NUM m')
    → m' < n
    → isHighestℕ {k} {w} {w} n name comp
→isHighestℕ-upd-body2-NUM4 cc {0} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom () g0 ltn
→isHighestℕ-upd-body2-NUM4 cc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom comp g0 ltn
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  (m' , g0 , ltn) ,
  ¬∈names→isHighestℕ cc {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {w} {w} {n} {name} (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m})) nnw idom (m' , g0 , ltn) comp





→isHighestℕ-upd-body2-NUM4-∈names𝕎 :
    (cc : ContConds) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET AX (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , w))
    → ∈names𝕎 {k} {w} {w} name comp
→isHighestℕ-upd-body2-NUM4-∈names𝕎 cc {0} {name} {w} {f} {m} {m'} cf nnf nnw idom ()
→isHighestℕ-upd-body2-NUM4-∈names𝕎 cc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  nnw , idom ,
  ¬∈names→∈names𝕎
    cc {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {w} {w} {name}
    (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
    nnw idom comp


→isHighestℕ-upd-body2-NUM2 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → compatible· name w Res⊤
    → (comp : steps k (LET (IFLT (NUM m') (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
    → getT 0 name w ≡ just (NUM m')
    → m' < n
    → getT≤ℕ (chooseT0if name w m' m) n name
    → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body2-NUM2 cc gc {0} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat () g0 ltn gtn
→isHighestℕ-upd-body2-NUM2 cc gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 ltn gtn with m' <? m
... | yes x = (m' , g0 , ltn) , →isHighestℕ-upd-body2-NUM3 cc gc {k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 ltn (getT≤ℕ-chooseT→ gc {name} {w} {n} {m} compat gtn)
... | no x = (m' , g0 , ltn) , →isHighestℕ-upd-body2-NUM4 cc {k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom comp g0 ltn



→isHighestℕ-upd-body2-NUM2-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET (IFLT (NUM m') (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
    → ∈names𝕎 {k} {w} {chooseT0if name w m' m} name comp
→isHighestℕ-upd-body2-NUM2-∈names𝕎 cc gc {0} {name} {w} {f} {m} {m'} cf nnf nnw idom ()
→isHighestℕ-upd-body2-NUM2-∈names𝕎 cc gc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp with m' <? m
... | yes x = nnw , idom , →isHighestℕ-upd-body2-NUM3-∈names𝕎 cc gc {k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp
... | no x = nnw , idom , →isHighestℕ-upd-body2-NUM4-∈names𝕎 cc {k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp



→isHighestℕ-upd-body2-NUM1 : (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
                             → # f
                             → ¬ name ∈ names f
                             → ¬ name ∈ names𝕎· w
                             → name ∈ dom𝕎· w
                             → compatible· name w Res⊤
                             → (comp : steps k (LET (IFLT (get0 name) (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
                             → getT 0 name w ≡ just (NUM m')
                             → m' < n
                             → getT≤ℕ (chooseT0if name w m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body2-NUM1 cc gc {0} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat () g0 len gtn
→isHighestℕ-upd-body2-NUM1 cc gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 len gtn rewrite g0 =
  (m' , g0 , len) ,
  →isHighestℕ-upd-body2-NUM2 cc gc {k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 len gtn



→isHighestℕ-upd-body2-NUM1-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET (IFLT (get0 name) (NUM m) (setT name (NUM m)) AX) (APPLY (shiftDown 1 (subv 1 (NUM m) (shiftUp 0 f))) (NUM m)) , w)
               ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
    → getT 0 name w ≡ just (NUM m')
    → ∈names𝕎 {k} {w} {chooseT0if name w m' m} name comp
→isHighestℕ-upd-body2-NUM1-∈names𝕎 cc gc {0} {name} {w} {f} {m} {m'} cf nnf nnw idom () g0
→isHighestℕ-upd-body2-NUM1-∈names𝕎 cc gc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp g0 rewrite g0 =
  nnw , idom ,
  →isHighestℕ-upd-body2-NUM2-∈names𝕎 cc gc {k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp



→isHighestℕ-upd-body2-NUM1b : (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w w' : 𝕎·} {b f : Term} {n m m' : ℕ}
                             → # f
                             → ¬ name ∈ names f
                             → ¬ name ∈ names𝕎· w
                             → name ∈ dom𝕎· w
                             → compatible· name w Res⊤
                             → b ≡ NUM m
                             → w ≡ w'
                             → (comp : steps k (LET (IFLT (get0 name) (shiftDown 0 (shiftUp 0 b)) (setT name (shiftDown 0 (shiftUp 0 b))) AX)
                                                     (APPLY (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 b)) (shiftUp 0 f)))
                                                            (shiftDown 1 (shiftUp 0 (shiftUp 0 b)))) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w' m' m))
                             → getT 0 name w' ≡ just (NUM m')
                             → m' < n
                             → getT≤ℕ (chooseT0if name w' m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w' m' m} n name comp
→isHighestℕ-upd-body2-NUM1b cc gc {k} {name} {w} {w'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat eqb eqw comp g0 len gtn
  rewrite eqb | eqw =
  →isHighestℕ-upd-body2-NUM1 cc gc {k} {name} {w'} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 len gtn



→isHighestℕ-upd-body2-NUM1b-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w w' : 𝕎·} {b f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → b ≡ NUM m
    → w ≡ w'
    → (comp : steps k (LET (IFLT (get0 name) (shiftDown 0 (shiftUp 0 b)) (setT name (shiftDown 0 (shiftUp 0 b))) AX)
                            (APPLY (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 b)) (shiftUp 0 f)))
                                   (shiftDown 1 (shiftUp 0 (shiftUp 0 b)))) , w)
               ≡ (APPLY f (NUM m) , chooseT0if name w' m' m))
    → getT 0 name w' ≡ just (NUM m')
    → ∈names𝕎 {k} {w} {chooseT0if name w' m' m} name comp
→isHighestℕ-upd-body2-NUM1b-∈names𝕎 cc gc {k} {name} {w} {w'} {b} {f} {m} {m'} cf nnf nnw idom eqb eqw comp g0
  rewrite eqb | eqw =
  →isHighestℕ-upd-body2-NUM1-∈names𝕎 cc gc {k} {name} {w'} {f} {m} {m'} cf nnf nnw idom comp g0



→isHighestℕ-upd-body2-NUM : (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {n m m' : ℕ}
                             → # f
                             → ¬ name ∈ names f
                             → ¬ name ∈ names𝕎· w
                             → name ∈ dom𝕎· w
                             → compatible· name w Res⊤
                             → (comp : steps k (LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w)
                                        ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
                             → getT 0 name w ≡ just (NUM m')
                             → m' < n
                             → getT≤ℕ (chooseT0if name w m' m) n name
                             → isHighestℕ {k} {w} {chooseT0if name w m' m} n name comp
→isHighestℕ-upd-body2-NUM cc gc {0} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat () g0 len gtn
→isHighestℕ-upd-body2-NUM cc gc {suc k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 len gtn =
  (m' , g0 , len) ,
  →isHighestℕ-upd-body2-NUM1 cc gc {k} {name} {w} {f} {n} {m} {m'} cf nnf nnw idom compat comp g0 len gtn



→isHighestℕ-upd-body2-NUM-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k : ℕ} {name : Name} {w : 𝕎·} {f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w
    → name ∈ dom𝕎· w
    → (comp : steps k (LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w)
               ≡ (APPLY f (NUM m) , chooseT0if name w m' m))
    → getT 0 name w ≡ just (NUM m')
    → ∈names𝕎 {k} {w} {chooseT0if name w m' m} name comp
→isHighestℕ-upd-body2-NUM-∈names𝕎 cc gc {0} {name} {w} {f} {m} {m'} cf nnf nnw idom () g0
→isHighestℕ-upd-body2-NUM-∈names𝕎 cc gc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp g0 =
  nnw , idom ,
  →isHighestℕ-upd-body2-NUM1-∈names𝕎 cc gc {k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp g0



→isHighestℕ-upd-body2 : (cc : ContConds) (gc : get-choose-ℕ) {k1 k2 : ℕ} {name : Name} {w1 w1' : 𝕎·} {b f : Term} {n m m' : ℕ}
                         → # f
                         → ¬ name ∈ names f
                         → ¬ name ∈ names𝕎· w1
                         → name ∈ dom𝕎· w1
                         → compatible· name w1 Res⊤
                         → (comp1 : steps k1 (b , w1) ≡ (NUM m , w1'))
                         → (comp2 : steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1)
                                     ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))
                         → getT 0 name w1' ≡ just (NUM m')
                         → getT≤ℕ (chooseT0if name w1' m' m) n name
                         → isHighestℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1
                         → ∈names𝕎 {k1} {w1} {w1'} {b} {NUM m} name comp1
                         → isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} n name comp2
→isHighestℕ-upd-body2 cc gc {0} {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat comp1 comp2 g0 gtn h inw
  rewrite pair-inj₁ comp1 | pair-inj₂ comp1 | g0 =
  →isHighestℕ-upd-body2-NUM cc gc {k2} {name} {w1'} {f} {n} {m} {m'} cf nnf nnw idom compat comp2 g0 (Σ≡justNUM≤ h) gtn
→isHighestℕ-upd-body2 cc gc {suc k1} {0} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat comp1 () g0 gtn h inw
→isHighestℕ-upd-body2 cc gc {suc k1} {suc k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat comp1 comp2 g0 gtn h inw with step⊎ b w1
... | inj₁ (b' , w' , z) rewrite z with isValue⊎ b
... |    inj₁ x
  rewrite stepVal b w1 x
        | sym (pair-inj₁ (just-inj z))
        | sym (pair-inj₂ (just-inj z)) =
  fst h , →isHighestℕ-upd-body2-NUM1b cc gc {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat eqb eqw comp2 g0 (getT-getT≤ℕ→ eqw g0 (fst h)) gtn
  where
    eqb : b ≡ NUM m
    eqb = stepsVal→ₗ b (NUM m) w1 w1' k1 x comp1

    eqw : w1 ≡ w1'
    eqw = stepsVal→ᵣ b (NUM m) w1 w1' k1 x comp1
... |    inj₂ x rewrite z =
  fst h , →isHighestℕ-upd-body2 cc gc {k1} {k2} {name} {w'} {w1'} {b'} {f} {n} {m} {m'} cf nnf
                                 (∈names𝕎→¬∈name𝕎 {k1} {w'} {w1'} {b'} {NUM m} name comp1 (snd (snd inw)))
                                 (∈names𝕎→∈dom𝕎 {k1} {w'} {w1'} {b'} {NUM m} name comp1 (snd (snd inw)))
                                 (⊑-compatible· (step⊑ {w1} {w'} {b} {b'} z) compat)
                                 comp1 comp2 g0 gtn (snd h) (snd (snd inw))
→isHighestℕ-upd-body2 cc gc {suc k1} {suc k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat comp1 comp2 g0 gtn h inw | inj₂ z
  rewrite z | pair-inj₁ comp1 | pair-inj₂ comp1 = ⊥-elim (¬just≡nothing z)


→isHighestℕ-upd-body2-∈names𝕎 :
    (cc : ContConds) (gc : get-choose-ℕ) {k1 k2 : ℕ} {name : Name} {w1 w1' : 𝕎·} {b f : Term} {m m' : ℕ}
    → # f
    → ¬ name ∈ names f
    → ¬ name ∈ names𝕎· w1
    → name ∈ dom𝕎· w1
    → (comp1 : steps k1 (b , w1) ≡ (NUM m , w1'))
    → (comp2 : steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1)
                ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))
    → getT 0 name w1' ≡ just (NUM m')
    → ∈names𝕎 {k1} {w1} {w1'} {b} {NUM m} name comp1
    → ∈names𝕎 {k2} {w1} {chooseT0if name w1' m' m} {LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} name comp2
→isHighestℕ-upd-body2-∈names𝕎 cc gc {0} {k2} {name} {w1} {w1'} {b} {f} {m} {m'} cf nnf nnw idom comp1 comp2 g0 inw
  rewrite pair-inj₁ comp1 | pair-inj₂ comp1 | g0
  = →isHighestℕ-upd-body2-NUM-∈names𝕎 cc gc {k2} {name} {w1'} {f} {m} {m'} cf nnf nnw idom comp2 g0
→isHighestℕ-upd-body2-∈names𝕎 cc gc {suc k1} {suc k2} {name} {w1} {w1'} {b} {f} {m} {m'} cf nnf nnw idom comp1 comp2 g0 inw with step⊎ b w1
... | inj₁ (b' , w' , z) rewrite z with isValue⊎ b
... |    inj₁ x
  rewrite stepVal b w1 x
        | sym (pair-inj₁ (just-inj z))
        | sym (pair-inj₂ (just-inj z)) =
  nnw , idom ,
  →isHighestℕ-upd-body2-NUM1b-∈names𝕎 cc gc {k2} {name} {w1} {w1'} {b} {f} {m} {m'} cf nnf nnw idom eqb eqw comp2 g0
  where
    eqb : b ≡ NUM m
    eqb = stepsVal→ₗ b (NUM m) w1 w1' k1 x comp1

    eqw : w1 ≡ w1'
    eqw = stepsVal→ᵣ b (NUM m) w1 w1' k1 x comp1
... |    inj₂ x rewrite z =
  nnw , idom ,
  →isHighestℕ-upd-body2-∈names𝕎
    cc gc {k1} {k2} {name} {w'} {w1'} {b'} {f} {m} {m'} cf nnf
    (∈names𝕎→¬∈name𝕎 {k1} {w'} {w1'} {b'} {NUM m} name comp1 (snd (snd inw)))
    (∈names𝕎→∈dom𝕎 {k1} {w'} {w1'} {b'} {NUM m} name comp1 (snd (snd inw)))
    comp1 comp2 g0 (snd (snd inw))
→isHighestℕ-upd-body2-∈names𝕎 cc gc {suc k1} {suc k2} {name} {w1} {w1'} {b} {f} {m} {m'} cf nnf nnw idom comp1 comp2 g0 inw | inj₂ z
  rewrite z | pair-inj₁ comp1 | pair-inj₂ comp1 = ⊥-elim (¬just≡nothing z)



→ΣhighestUpdCtxt2-upd : (cc : ContConds) (gc : get-choose-ℕ) {name : Name} {f b : Term} {w1 : 𝕎·} {n : ℕ}
                        → compatible· name w1 Res⊤
                        → ∀𝕎-get0-NUM w1 name
                        → # f
                        → ¬ name ∈ names f
                        → ¬ name ∈ names𝕎· w1
                        → name ∈ dom𝕎· w1
                        → updCtxt2 name f b
                        → stepsPresHighestℕ2 name f (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
                        → ΣhighestUpdCtxt2 name f n (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
→ΣhighestUpdCtxt2-upd cc gc {name} {f} {b} {w1} {n} compat wgt0 cf nnf nnw idom nnb (k , v , w2 , comp , isv , ind) =
  k2 , APPLY f (NUM m) , chooseT0if name w1' m' m , comp2 , j , inw  ,
  updCtxt2-refl name f (APPLY f (NUM m)) (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
  where
    c : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1' → Σ ℕ (λ m → Σ ℕ (λ m' →
           k1 < k
           × k2 < k
           × getT 0 name w1' ≡ just (NUM m')
           × ssteps k1 (b , w1) ≡ just (NUM m , w1')
           × steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))))))
    c = upd-decomp cf wgt0 comp isv

    k1 : ℕ
    k1 = fst c

    k2 : ℕ
    k2 = fst (snd c)

    w1' : 𝕎·
    w1' = fst (snd (snd c))

    m : ℕ
    m = fst (snd (snd (snd c)))

    m' : ℕ
    m' = fst (snd (snd (snd (snd c))))

    ltk1 : k1 < k
    ltk1 = fst (snd (snd (snd (snd (snd c)))))

    ltk2 : k2 < k
    ltk2 = fst (snd (snd (snd (snd (snd (snd c))))))

    gt0 : getT 0 name w1' ≡ just (NUM m')
    gt0 = fst (snd (snd (snd (snd (snd (snd (snd c)))))))

    comp1 : ssteps k1 (b , w1) ≡ just (NUM m , w1')
    comp1 = fst (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    comp1b : steps k1 (b , w1) ≡ (NUM m , w1')
    comp1b = ssteps→steps {k1} {b} {NUM m} {w1} {w1'} comp1

    comp2 : steps k2 (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m)
    comp2 = snd (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    e1 : w1 ⊑· w1'
    e1 = steps→⊑ k1 b (NUM m) comp1b

    ind' : (getT≤ℕ w1' n name → isHighestℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1b)
           × ∈names𝕎 {k1} {w1} {w1'} {b} {NUM m} name comp1b
    ind' = ind k1 (<⇒≤ ltk1) {w1} {w1'} {b} {NUM m} {n} comp1b tt nnb compat wgt0 nnw idom

    j : getT≤ℕ (chooseT0if name w1' m' m) n name
         → (getT≤ℕ w1 n name × isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} n name comp2)
    j g = isHighestℕ→getT≤ℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1b (fst ind' g') , j1
      where
        g' : getT≤ℕ w1' n name
        g' = getT≤ℕ-chooseT0if→ gc {w1'} {name} {n} {m} {m'} (⊑-compatible· e1 compat) gt0 g

        j1 : isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} {LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} n name comp2
        j1 = →isHighestℕ-upd-body2 cc gc {k1} {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat comp1b comp2 gt0 g (fst ind' g') (snd ind')

    inw : ∈names𝕎 {k2} {w1} {chooseT0if name w1' m' m} name comp2
    inw = →isHighestℕ-upd-body2-∈names𝕎 cc gc {k1} {k2} {name} {w1} {w1'} {b} {f} {m} {m'} cf nnf nnw idom comp1b comp2 gt0 (snd ind')



ΣhighestUpdCtxtAux2-APPLY₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (APPLY a1 b) (APPLY a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (APPLY a b) (APPLY a' b) w0 w w'
ΣhighestUpdCtxtAux2-APPLY₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-LAM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p with is-CS a
... |    inj₁ (y , q) rewrite q = ⊥-elim (nv tt)
... |    inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-APPLY₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (APPLY a b) (APPLY a' b) w0 w w')
ΣhighestUpdCtxtAux2-APPLY₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-APPLY _ _ u ub
ΣhighestUpdCtxtAux2-APPLY₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-APPLY₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-APPLY₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (APPLY a1 b) (APPLY a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-APPLY₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-APPLY₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-APPLY _ _ u ub



ΣhighestUpdCtxt2-APPLY₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (APPLY a b) w0 w
ΣhighestUpdCtxt2-APPLY₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , inw , u) =
  fst q , APPLY a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (APPLY a b) (APPLY a' b) w0 w w')
    q = ΣhighestUpdCtxtAux2-APPLY₁ {k} ub (wcomp , i , inw , u)



ΣhighestUpdCtxtAux2-APPLY₂-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {name' : Name} {b b1 b' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue b
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step b w ≡ just (b1 , w1)
                               → (comp : steps k (b1 , w1) ≡ (b' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {b1} {b'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (APPLY (CS name') b1) (APPLY (CS name') b') w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (APPLY (CS name') b) (APPLY (CS name') b') w0 w w'
ΣhighestUpdCtxtAux2-APPLY₂-aux {j} {k} {w} {w0} {w1} {w'} {name'} {b} {b1} {b'} {name} {f} {n} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM b
... | inj₁ (m , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-APPLY₂ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {name' : Name} {b b' : Term} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux2 k name f n b b' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (APPLY (CS name') b) (APPLY (CS name') b') w0 w w')
ΣhighestUpdCtxtAux2-APPLY₂ {0} {name} {f} {n} {name'} {b} {b'} {w0} {w} {w'} (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-APPLY _ _ (updCtxt2-CS name') u
ΣhighestUpdCtxtAux2-APPLY₂ {suc k} {name} {f} {n} {name'} {b} {b'} {w0} {w} {w'} (comp , i , inw , u) with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ y rewrite stepVal b w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-APPLY₂ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-APPLY₂-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (APPLY (CS name') b1) (APPLY (CS name') b') w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-APPLY₂ {k} {name} {f} {n} {name'} {b1} {b'} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-APPLY₂ {suc k} {name} {f} {n} {name'} {b} {b'} {w0} {w} {w'} (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-APPLY _ _ (updCtxt2-CS name') u



ΣhighestUpdCtxt2-APPLY₂ : {name : Name} {f : Term} {n : ℕ} {name' : Name} {b : Term} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt2 name f n b w0 w
                        → ΣhighestUpdCtxt2 name f n (APPLY (CS name') b) w0 w
ΣhighestUpdCtxt2-APPLY₂ {name} {f} {n} {name'} {b} {w0} {w} (k , b' , w' , wcomp , i , inw , u) =
  fst q , APPLY (CS name') b' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (APPLY (CS name') b) (APPLY (CS name') b') w0 w w')
    q = ΣhighestUpdCtxtAux2-APPLY₂ {k} (wcomp , i , inw , u)



stepsPresHighestℕ2-APPLY₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (APPLY a b) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-APPLY₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = APPLY→hasValue k a b v w w' comp isv



APPLY→hasValue₂ : (k : ℕ) (name : Name) (b v : Term) (w w' : 𝕎·)
                 → steps k (APPLY (CS name) b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k b w
APPLY→hasValue₂ 0 name b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
APPLY→hasValue₂ (suc k) name b v w w' comp isv with is-NUM b
... | inj₁ (m , p) rewrite p = isValue→hasValueℕ (suc k) (NUM m) w tt
... | inj₂ p with step⊎ b w
... |    inj₁ (b' , w'' , z) rewrite z = APPLY→hasValue₂ k name b' v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


stepsPresHighestℕ2-APPLY₂→ : {name : Name} {f : Term} {name' : Name} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (APPLY (CS name') a) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-APPLY₂→ {name} {f} {name'} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = APPLY→hasValue₂ k name' a v w w' comp isv





stepsPresHighestℕ2-IFLT₂→ : {name : Name} {f : Term} {n : ℕ} {b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (IFLT (NUM n) b c d) w
                            → stepsPresHighestℕ2 name f b w
stepsPresHighestℕ2-IFLT₂→ {name} {f} {n} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k b w
    hv = IFLT-NUM→hasValue k n b c d v w w' comp isv



ΣhighestUpdCtxtAux2-IFLT₂-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {b b1 b' : Term} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {c d : Term}
                               → ¬ isValue b
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step b w ≡ just (b1 , w1)
                               → (comp : steps k (b1 , w1) ≡ (b' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {b1} {b'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (IFLT (NUM m) b1 c d) (IFLT (NUM m) b' c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (IFLT (NUM m) b c d) (IFLT (NUM m) b' c d) w0 w w'
ΣhighestUpdCtxtAux2-IFLT₂-aux {j} {k} {w} {w0} {w1} {w'} {b} {b1} {b'} {name} {f} {n} {m} {c} {d} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM b
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-IFLT₂ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b b' c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxtAux2 k name f n b b' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFLT (NUM m) b c d) (IFLT (NUM m) b' c d) w0 w w')
ΣhighestUpdCtxtAux2-IFLT₂ {0} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFLT _ _ _ _ (updCtxt2-NUM m) u uc ud
ΣhighestUpdCtxtAux2-IFLT₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , inw , u) with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ y rewrite stepVal b w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-IFLT₂ {k} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-IFLT₂-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFLT (NUM m) b1 c d) (IFLT (NUM m) b' c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-IFLT₂ {k} {name} {f} {n} {m} {b1} {b'} {c} {d} {w0} {w1} {w'} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-IFLT₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFLT _ _ _ _ (updCtxt2-NUM m) u uc ud



ΣhighestUpdCtxt2-IFLT₂ : {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b c d : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxt2 name f n b w0 w
                        → ΣhighestUpdCtxt2 name f n (IFLT (NUM m) b c d) w0 w
ΣhighestUpdCtxt2-IFLT₂ {name} {f} {n} {m} {b} {c} {d} {w0} {w} uc ud (k , b' , w' , wcomp , i , inw , u) =
  fst q , IFLT (NUM m) b' c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFLT (NUM m) b c d) (IFLT (NUM m) b' c d) w0 w w')
    q = ΣhighestUpdCtxtAux2-IFLT₂ {k} uc ud (wcomp , i , inw , u)



stepsPresHighestℕ2-IFLT₁→ : {name : Name} {f : Term} {a b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (IFLT a b c d) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-IFLT₁→ {name} {f} {a} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = IFLT→hasValue k a b c d v w w' comp isv



ΣhighestUpdCtxtAux2-IFLT₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b c d : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (IFLT a1 b c d) (IFLT a' b c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (IFLT a b c d) (IFLT a' b c d) w0 w w'
ΣhighestUpdCtxtAux2-IFLT₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} {c} {d} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-IFLT₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFLT a b c d) (IFLT a' b c d) w0 w w')
ΣhighestUpdCtxtAux2-IFLT₁ {0} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFLT _ _ _ _ u ub uc ud
ΣhighestUpdCtxtAux2-IFLT₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-IFLT₁ {k} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-IFLT₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFLT a1 b c d) (IFLT a' b c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-IFLT₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {d} {w0} {w1} {w'} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-IFLT₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFLT _ _ _ _ u ub uc ud



ΣhighestUpdCtxt2-IFLT₁ : {name : Name} {f : Term} {n : ℕ} {a b c d : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (IFLT a b c d) w0 w
ΣhighestUpdCtxt2-IFLT₁ {name} {f} {n} {a} {b} {c} {d} {w0} {w} ub uc ud (k , a' , w' , wcomp , i , inw , u) =
  fst q , IFLT a' b c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFLT a b c d) (IFLT a' b c d) w0 w w')
    q = ΣhighestUpdCtxtAux2-IFLT₁ {k} ub uc ud (wcomp , i , inw , u)




ΣhighestUpdCtxtAux2-SUC₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (SUC a1) (SUC a') w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (SUC a) (SUC a') w0 w w'
ΣhighestUpdCtxtAux2-SUC₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-SUC₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' : Term} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (SUC a) (SUC a') w0 w w')
ΣhighestUpdCtxtAux2-SUC₁ {0} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-SUC _ u
ΣhighestUpdCtxtAux2-SUC₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-SUC₁ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-SUC₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (SUC a1) (SUC a') w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-SUC₁ {k} {name} {f} {n} {a1} {a'} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-SUC₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-SUC _ u



ΣhighestUpdCtxt2-SUC₁ : {name : Name} {f : Term} {n : ℕ} {a : Term} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (SUC a) w0 w
ΣhighestUpdCtxt2-SUC₁ {name} {f} {n} {a} {w0} {w} (k , a' , w' , wcomp , i , inw , u) =
  fst q , SUC a' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (SUC a) (SUC a') w0 w w')
    q = ΣhighestUpdCtxtAux2-SUC₁ {k} (wcomp , i , inw , u)



stepsPresHighestℕ2-SUC₁→ : {name : Name} {f : Term} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (SUC a) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-SUC₁→ {name} {f} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = SUC→hasValue k a v w w' comp isv



ΣhighestUpdCtxtAux2-FIX₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (FIX a1) (FIX a') w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (FIX a) (FIX a') w0 w w'
ΣhighestUpdCtxtAux2-FIX₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-LAM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-FIX₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' : Term} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (FIX a) (FIX a') w0 w w')
ΣhighestUpdCtxtAux2-FIX₁ {0} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-FIX _ u
ΣhighestUpdCtxtAux2-FIX₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-FIX₁ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-FIX₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (FIX a1) (FIX a') w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-FIX₁ {k} {name} {f} {n} {a1} {a'} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-FIX₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-FIX _ u



ΣhighestUpdCtxt2-FIX₁ : {name : Name} {f : Term} {n : ℕ} {a : Term} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (FIX a) w0 w
ΣhighestUpdCtxt2-FIX₁ {name} {f} {n} {a} {w0} {w} (k , a' , w' , wcomp , i , inw , u) =
  fst q , FIX a' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (FIX a) (FIX a') w0 w w')
    q = ΣhighestUpdCtxtAux2-FIX₁ {k} (wcomp , i , inw , u)



stepsPresHighestℕ2-FIX₁→ : {name : Name} {f : Term} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (FIX a) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-FIX₁→ {name} {f} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = FIX→hasValue k a v w w' comp isv


ΣhighestUpdCtxtAux2-LET₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (LET a1 b) (LET a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (LET a b) (LET a' b) w0 w w'
ΣhighestUpdCtxtAux2-LET₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv nnw idom comp0 comp i (comp1 , g , inw , u) with isValue⊎ a
... | inj₁ x = ⊥-elim (nv x)
... | inj₂ x rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-LET₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (LET a b) (LET a' b) w0 w w')
ΣhighestUpdCtxtAux2-LET₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-LET _ _ u ub
ΣhighestUpdCtxtAux2-LET₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-LET₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-LET₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (LET a1 b) (LET a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-LET₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-LET₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-LET _ _ u ub



ΣhighestUpdCtxt2-LET₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (LET a b) w0 w
ΣhighestUpdCtxt2-LET₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , inw , u) =
  fst q , LET a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (LET a b) (LET a' b) w0 w w')
    q = ΣhighestUpdCtxtAux2-LET₁ {k} ub (wcomp , i , inw , u)



stepsPresHighestℕ2-LET₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (LET a b) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-LET₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = LET→hasValue k a b v w w' comp isv


stepsPresHighestℕ2-SPREAD₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (SPREAD a b) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-SPREAD₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = SPREAD→hasValue k a b v w w' comp isv


stepsPresHighestℕ2-DECIDE₁→ : {name : Name} {f : Term} {a b c : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (DECIDE a b c) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-DECIDE₁→ {name} {f} {a} {b} {c} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = DECIDE→hasValue k a b c v w w' comp isv



stepsPresHighestℕ2-CHOOSE₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (CHOOSE a b) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-CHOOSE₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = CHOOSE→hasValue k a b v w w' comp isv



ΣhighestUpdCtxtAux2-SPREAD₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (SPREAD a1 b) (SPREAD a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (SPREAD a b) (SPREAD a' b) w0 w w'
ΣhighestUpdCtxtAux2-SPREAD₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-PAIR a
... | inj₁ (x , y , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-SPREAD₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (SPREAD a b) (SPREAD a' b) w0 w w')
ΣhighestUpdCtxtAux2-SPREAD₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-SPREAD _ _ u ub
ΣhighestUpdCtxtAux2-SPREAD₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-SPREAD₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-SPREAD₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (SPREAD a1 b) (SPREAD a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-SPREAD₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-SPREAD₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-SPREAD _ _ u ub



ΣhighestUpdCtxt2-SPREAD₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (SPREAD a b) w0 w
ΣhighestUpdCtxt2-SPREAD₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , inw , u) =
  fst q , SPREAD a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (SPREAD a b) (SPREAD a' b) w0 w w')
    q = ΣhighestUpdCtxtAux2-SPREAD₁ {k} ub (wcomp , i , inw , u)




ΣhighestUpdCtxtAux2-DECIDE₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b c : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (DECIDE a1 b c) (DECIDE a' b c) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (DECIDE a b c) (DECIDE a' b c) w0 w w'
ΣhighestUpdCtxtAux2-DECIDE₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} {c} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-INL a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p with is-INR a
... |    inj₁ (y , q) rewrite q = ⊥-elim (nv tt)
... |    inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-DECIDE₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (DECIDE a b c) (DECIDE a' b c) w0 w w')
ΣhighestUpdCtxtAux2-DECIDE₁ {0} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-DECIDE _ _ _ u ub uc
ΣhighestUpdCtxtAux2-DECIDE₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-DECIDE₁ {k} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-DECIDE₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (DECIDE a1 b c) (DECIDE a' b c) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-DECIDE₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {w0} {w1} {w'} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-DECIDE₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-DECIDE _ _ _ u ub uc



ΣhighestUpdCtxt2-DECIDE₁ : {name : Name} {f : Term} {n : ℕ} {a b c : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (DECIDE a b c) w0 w
ΣhighestUpdCtxt2-DECIDE₁ {name} {f} {n} {a} {b} {c} {w0} {w} ub uc (k , a' , w' , wcomp , i , inw , u) =
  fst q , DECIDE a' b c , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (DECIDE a b c) (DECIDE a' b c) w0 w w')
    q = ΣhighestUpdCtxtAux2-DECIDE₁ {k} ub uc (wcomp , i , inw , u)



ΣhighestUpdCtxtAux2-CHOOSE₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (CHOOSE a1 b) (CHOOSE a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (CHOOSE a b) (CHOOSE a' b) w0 w w'
ΣhighestUpdCtxtAux2-CHOOSE₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NAME a
... | inj₁ (name' , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-CHOOSE₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (CHOOSE a b) (CHOOSE a' b) w0 w w')
ΣhighestUpdCtxtAux2-CHOOSE₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-CHOOSE _ _ u ub
ΣhighestUpdCtxtAux2-CHOOSE₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-CHOOSE₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-CHOOSE₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (CHOOSE a1 b) (CHOOSE a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-CHOOSE₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-CHOOSE₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-CHOOSE _ _ u ub



ΣhighestUpdCtxt2-CHOOSE₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (CHOOSE a b) w0 w
ΣhighestUpdCtxt2-CHOOSE₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , inw , u) =
  fst q , CHOOSE a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (CHOOSE a b) (CHOOSE a' b) w0 w w')
    q = ΣhighestUpdCtxtAux2-CHOOSE₁ {k} ub (wcomp , i , inw , u)



¬∈names𝕎→¬∈names : (cc : ContConds) (name name' : Name) (n : ℕ) (t : Term) (w : 𝕎·)
                     → getT n name' w ≡ just t
                     → ¬ name ∈ names𝕎· w
                     → ¬ name ∈ names t
¬∈names𝕎→¬∈names cc name name' n t w gt nn i =
  nn (ContConds.ccGnames cc name name' n t w gt i)



¬∈names𝕎→updCtxt2 : (cc : ContConds) (f : Term) (name name' : Name) (n : ℕ) (t : Term) (w : 𝕎·)
                     → getT n name' w ≡ just t
                     → ¬ name ∈ names𝕎· w
                     → updCtxt2 name f t
¬∈names𝕎→updCtxt2 cc f name name' n t w gt nn =
  updCtxt2-refl name f t (¬∈names𝕎→¬∈names cc name name' n t w gt nn)




{--
predIf≤-inj : {n : ℕ} {x y : Var} → predIf≤ n x ≡ predIf≤ n y → x ≡ y
predIf≤-inj {n} {0} {0} e = refl
predIf≤-inj {n} {0} {suc y} e with suc y ≤? n
... | yes q = e
... | no q  = {!!}
predIf≤-inj {n} {suc x} {0} e with suc x ≤? n
... | yes p = e
... | no p  = {!!}
predIf≤-inj {n} {suc x} {suc y} e with suc x ≤? n | suc y ≤? n
... | yes p | yes q = e
... | yes p | no q rewrite e = ⊥-elim {!!}
... | no p  | yes q rewrite e = {!!}
... | no p  | no q  rewrite e = refl
--}



fvars-shiftNameDown : (n : ℕ) (a : Term) → fvars (shiftNameDown n a) ≡ fvars a
fvars-shiftNameDown n (VAR x) = refl
fvars-shiftNameDown n NAT = refl
fvars-shiftNameDown n QNAT = refl
fvars-shiftNameDown n (LT a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (QLT a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (NUM x) = refl
fvars-shiftNameDown n (IFLT a a₁ a₂ a₃) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ | fvars-shiftNameDown n a₃ = refl
fvars-shiftNameDown n (SUC a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (PI a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (LAMBDA a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (APPLY a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (FIX a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (LET a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (SUM a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (PAIR a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (SPREAD a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (SET a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (ISECT a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (TUNION a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (UNION a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (QTUNION a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (INL a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (INR a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (DECIDE a a₁ a₂) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ = refl
fvars-shiftNameDown n (EQ a a₁ a₂) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ = refl
fvars-shiftNameDown n AX = refl
fvars-shiftNameDown n FREE = refl
fvars-shiftNameDown n (CS x) = refl
fvars-shiftNameDown n (NAME x) = refl
fvars-shiftNameDown n (FRESH a) rewrite fvars-shiftNameDown (suc n) a = refl
fvars-shiftNameDown n (CHOOSE a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
--fvars-shiftNameDown n (IFC0 a a₁ a₂) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ = refl
fvars-shiftNameDown n (TSQUASH a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (TTRUNC a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (TCONST a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (SUBSING a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (DUM a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (FFDEFS a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n PURE = refl
fvars-shiftNameDown n (UNIV x) = refl
fvars-shiftNameDown n (LIFT a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (LOWER a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (SHRINK a) rewrite fvars-shiftNameDown n a = refl


→#shiftNameDown : (n : ℕ) {a : Term} → # a → # shiftNameDown n a
→#shiftNameDown n {a} ca rewrite fvars-shiftNameDown n a = ca


≤→¬<→≡ : {i n : ℕ} → n ≤ i → ¬ n < i → i ≡ n
≤→¬<→≡ {i} {n} lei nlei = sym (<s→¬<→≡ {n} {i} (_≤_.s≤s lei) nlei)


sucIf≤-predIf≤ : (n : ℕ) (x : Name) → ¬ x ≡ n → (x ≡ 0 → 0 < n) → sucIf≤ n (predIf≤ n x) ≡ x
sucIf≤-predIf≤ n 0 d len with 0 <? n
... | yes p = refl
... | no p = ⊥-elim (p (len refl))
sucIf≤-predIf≤ n (suc x) d len with suc x ≤? n
... | yes p with suc x <? n
... |    yes q = refl
... |    no q = ⊥-elim (d (sym (≤→¬<→≡ {n} {suc x} p q) ))
sucIf≤-predIf≤ n (suc x) d len | no p with x <? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl



shiftNameUpDown : (n : ℕ) (t : Term)
                  → ((x : Name) → x ∈ names t → ¬ x ≡ n)
                  → (0 ∈ names t → 0 < n)
                  → shiftNameUp n (shiftNameDown n t) ≡ t
shiftNameUpDown n (VAR x) imp1 imp2 = refl
shiftNameUpDown n NAT imp1 imp2 = refl
shiftNameUpDown n QNAT imp1 imp2 = refl
shiftNameUpDown n (LT t t₁) imp1 imp2 = ≡LT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (QLT t t₁) imp1 imp2 = ≡QLT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (NUM x) imp1 imp2 = refl
shiftNameUpDown n (IFLT t t₁ t₂ t₃) imp1 imp2 = ≡IFLT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ˡ i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ˡ z)))) (shiftNameUpDown n t₂ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ i)))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ z))))) (shiftNameUpDown n t₃ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) i)))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) z)))))
shiftNameUpDown n (SUC t) imp1 imp2 = ≡SUC (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (PI t t₁) imp1 imp2 = ≡PI (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (LAMBDA t) imp1 imp2 = ≡LAMBDA (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (APPLY t t₁) imp1 imp2 = ≡APPLY (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (FIX t) imp1 imp2 = ≡FIX (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (LET t t₁) imp1 imp2 = ≡LET (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (SUM t t₁) imp1 imp2 = ≡SUM (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (PAIR t t₁) imp1 imp2 = ≡PAIR (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (SPREAD t t₁) imp1 imp2 = ≡SPREAD (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (SET t t₁) imp1 imp2 = ≡SET (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (TUNION t t₁) imp1 imp2 = ≡TUNION (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (ISECT t t₁) imp1 imp2 = ≡ISECT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (UNION t t₁) imp1 imp2 = ≡UNION (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (QTUNION t t₁) imp1 imp2 = ≡QTUNION (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (INL t) imp1 imp2 = ≡INL (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (INR t) imp1 imp2 = ≡INR (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (DECIDE t t₁ t₂) imp1 imp2 = ≡DECIDE (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ˡ i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ˡ z)))) (shiftNameUpDown n t₂ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) z))))
shiftNameUpDown n (EQ t t₁ t₂) imp1 imp2 = ≡EQ (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ˡ i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ˡ z)))) (shiftNameUpDown n t₂ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) z))))
shiftNameUpDown n AX imp1 imp2 = refl
shiftNameUpDown n FREE imp1 imp2 = refl
shiftNameUpDown n (CS x) imp1 imp2 = ≡CS (sucIf≤-predIf≤ n x (imp1 x (here refl)) (λ z → imp2 (here (sym z))))
shiftNameUpDown n (NAME x) imp1 imp2 = ≡NAME (sucIf≤-predIf≤ n x (imp1 x (here refl)) (λ z → imp2 (here (sym z))))
shiftNameUpDown n (FRESH t) imp1 imp2 = ≡FRESH (shiftNameUpDown (suc n) t imp1' λ z → _≤_.s≤s _≤_.z≤n)
  where
    imp1' : (x : Name) → x ∈ names t → ¬ x ≡ suc n
    imp1' x i z rewrite z = imp1 n (suc→∈lowerNames {n} {names t} i) refl
shiftNameUpDown n (CHOOSE t t₁) imp1 imp2 = ≡CHOOSE (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (TSQUASH t) imp1 imp2 = ≡TSQUASH (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (TTRUNC t) imp1 imp2 = ≡TTRUNC (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (TCONST t) imp1 imp2 = ≡TCONST (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (SUBSING t) imp1 imp2 = ≡SUBSING (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (DUM t) imp1 imp2 = ≡DUM (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (FFDEFS t t₁) imp1 imp2 = ≡FFDEFS (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n PURE imp1 imp2 = refl
shiftNameUpDown n (UNIV x) imp1 imp2 = refl
shiftNameUpDown n (LIFT t) imp1 imp2 = ≡LIFT (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (LOWER t) imp1 imp2 = ≡LOWER (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (SHRINK t) imp1 imp2 = ≡SHRINK (shiftNameUpDown n t imp1 imp2)


→updCtxt2-shiftNameDown : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                           → ((x : Name) → x ∈ names a → ¬ x ≡ v)
                           → (0 ∈ names a → 0 < v)
                           → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) a
                           → updCtxt2 name f (shiftNameDown v a)
→updCtxt2-shiftNameDown v {name} {f} cf {a} imp1 imp2 upd =
  updCtxt2-shiftNameUp→ v {name} {f} cf {shiftNameDown v a} upd1
  where
    upd1 : updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v (shiftNameDown v a))
    upd1 rewrite shiftNameUpDown v a imp1 imp2 = upd



→¬s∈names-shiftNameUp : (n : Name) (t : Term)
                         → ¬ n ∈ names t
                         → ¬ suc n ∈ names (shiftNameUp 0 t)
→¬s∈names-shiftNameUp n t ni z rewrite names-shiftNameUp≡ 0 t with ∈-map⁻ (sucIf≤ 0) z
... | (y , j , e) rewrite suc-injective e = ni j



renn¬∈ : (n m : Name) (t : Term)
         → ¬ n ∈ names t
         → renn n m t ≡ t
renn¬∈ n m (VAR x) ni = refl
renn¬∈ n m NAT ni = refl
renn¬∈ n m QNAT ni = refl
renn¬∈ n m (LT t t₁) ni = ≡LT (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (QLT t t₁) ni = ≡QLT (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (NUM x) ni = refl
renn¬∈ n m (IFLT t t₁ t₂ t₃) ni = ≡IFLT (renn¬∈ n m t (¬∈++4→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni)) (renn¬∈ n m t₁ (¬∈++4→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni)) (renn¬∈ n m t₂ (¬∈++4→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni)) (renn¬∈ n m t₃ (¬∈++4→¬∈4 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni))
renn¬∈ n m (SUC t) ni = ≡SUC (renn¬∈ n m t ni)
renn¬∈ n m (PI t t₁) ni = ≡PI (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (LAMBDA t) ni = ≡LAMBDA (renn¬∈ n m t ni)
renn¬∈ n m (APPLY t t₁) ni = ≡APPLY (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (FIX t) ni = ≡FIX (renn¬∈ n m t ni)
renn¬∈ n m (LET t t₁) ni = ≡LET (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (SUM t t₁) ni = ≡SUM (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (PAIR t t₁) ni = ≡PAIR (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (SPREAD t t₁) ni = ≡SPREAD (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (SET t t₁) ni = ≡SET (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (TUNION t t₁) ni = ≡TUNION (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (ISECT t t₁) ni = ≡ISECT (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (UNION t t₁) ni = ≡UNION (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (QTUNION t t₁) ni = ≡QTUNION (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (INL t) ni = ≡INL (renn¬∈ n m t ni)
renn¬∈ n m (INR t) ni = ≡INR (renn¬∈ n m t ni)
renn¬∈ n m (DECIDE t t₁ t₂) ni = ≡DECIDE (renn¬∈ n m t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {n} ni))
renn¬∈ n m (EQ t t₁ t₂) ni = ≡EQ (renn¬∈ n m t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {n} ni))
renn¬∈ n m AX ni = refl
renn¬∈ n m FREE ni = refl
renn¬∈ n m (CS x) ni with x ≟ n
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = refl
renn¬∈ n m (NAME x) ni with x ≟ n
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = refl
renn¬∈ n m (FRESH t) ni = ≡FRESH (renn¬∈ (suc n) (suc m) t (λ z → ni (suc→∈lowerNames {n} {names t} z)))
renn¬∈ n m (CHOOSE t t₁) ni = ≡CHOOSE (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (TSQUASH t) ni = ≡TSQUASH (renn¬∈ n m t ni)
renn¬∈ n m (TTRUNC t) ni = ≡TTRUNC (renn¬∈ n m t ni)
renn¬∈ n m (TCONST t) ni = ≡TCONST (renn¬∈ n m t ni)
renn¬∈ n m (SUBSING t) ni = ≡SUBSING (renn¬∈ n m t ni)
renn¬∈ n m (DUM t) ni = ≡DUM (renn¬∈ n m t ni)
renn¬∈ n m (FFDEFS t t₁) ni = ≡FFDEFS (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m PURE ni = refl
renn¬∈ n m (UNIV x) ni = refl
renn¬∈ n m (LIFT t) ni = ≡LIFT (renn¬∈ n m t ni)
renn¬∈ n m (LOWER t) ni = ≡LOWER (renn¬∈ n m t ni)
renn¬∈ n m (SHRINK t) ni = ≡SHRINK (renn¬∈ n m t ni)



updCtxt2-renn : (name n m : Name) (f a : Term)
                → ¬ name ≡ n
                → ¬ name ≡ m
                → ¬ n ∈ names f
                → # f
                → updCtxt2 name f a
                → updCtxt2 name f (renn n m a)
updCtxt2-renn name n m f .(VAR x) diff1 diff2 nf cf (updCtxt2-VAR x) = updCtxt2-VAR _
updCtxt2-renn name n m f .NAT diff1 diff2 nf cf updCtxt2-NAT = updCtxt2-NAT
updCtxt2-renn name n m f .QNAT diff1 diff2 nf cf updCtxt2-QNAT = updCtxt2-QNAT
updCtxt2-renn name n m f .(LT a b) diff1 diff2 nf cf (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(QLT a b) diff1 diff2 nf cf (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(NUM x) diff1 diff2 nf cf (updCtxt2-NUM x) = updCtxt2-NUM _
updCtxt2-renn name n m f .(IFLT a b c d) diff1 diff2 nf cf (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃) (updCtxt2-renn name n m f d diff1 diff2 nf cf upd₄)
updCtxt2-renn name n m f .(SUC a) diff1 diff2 nf cf (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(PI a b) diff1 diff2 nf cf (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(LAMBDA a) diff1 diff2 nf cf (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(APPLY a b) diff1 diff2 nf cf (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(FIX a) diff1 diff2 nf cf (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(LET a b) diff1 diff2 nf cf (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(SUM a b) diff1 diff2 nf cf (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(PAIR a b) diff1 diff2 nf cf (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(SPREAD a b) diff1 diff2 nf cf (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(SET a b) diff1 diff2 nf cf (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(ISECT a b) diff1 diff2 nf cf (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(TUNION a b) diff1 diff2 nf cf (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(UNION a b) diff1 diff2 nf cf (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(QTUNION a b) diff1 diff2 nf cf (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(INL a) diff1 diff2 nf cf (updCtxt2-INL a upd₁) = updCtxt2-INL _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(INR a) diff1 diff2 nf cf (updCtxt2-INR a upd₁) = updCtxt2-INR _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(DECIDE a b c) diff1 diff2 nf cf (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃)
updCtxt2-renn name n m f .(EQ a b c) diff1 diff2 nf cf (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃)
updCtxt2-renn name n m f .AX diff1 diff2 nf cf updCtxt2-AX = updCtxt2-AX
updCtxt2-renn name n m f .FREE diff1 diff2 nf cf updCtxt2-FREE = updCtxt2-FREE
updCtxt2-renn name n m f .(CS name') diff1 diff2 nf cf (updCtxt2-CS name') with name' ≟ n
... | yes _ = updCtxt2-CS _
... | no _ = updCtxt2-CS _
updCtxt2-renn name n m f .(NAME name') diff1 diff2 nf cf (updCtxt2-NAME name' x) with name' ≟ n
... | yes _ = updCtxt2-NAME _ (λ z → diff2 (sym z))
... | no _ = updCtxt2-NAME _ x
updCtxt2-renn name n m f .(FRESH a) diff1 diff2 nf cf (updCtxt2-FRESH a upd₁) = updCtxt2-FRESH _ (updCtxt2-renn (suc name) (suc n) (suc m) (shiftNameUp 0 f) a (λ z → diff1 (suc-injective z)) (λ z → diff2 (suc-injective z)) (→¬s∈names-shiftNameUp n f nf) (→#shiftNameUp 0 {f} cf) upd₁)
updCtxt2-renn name n m f .(CHOOSE a b) diff1 diff2 nf cf (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(TSQUASH a) diff1 diff2 nf cf (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(TTRUNC a) diff1 diff2 nf cf (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(TCONST a) diff1 diff2 nf cf (updCtxt2-TCONST a upd₁) = updCtxt2-TCONST _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(SUBSING a) diff1 diff2 nf cf (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .PURE diff1 diff2 nf cf updCtxt2-PURE = updCtxt2-PURE
updCtxt2-renn name n m f .(DUM a) diff1 diff2 nf cf (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(FFDEFS a b) diff1 diff2 nf cf (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
updCtxt2-renn name n m f .(UNIV x) diff1 diff2 nf cf (updCtxt2-UNIV x) = updCtxt2-UNIV _
updCtxt2-renn name n m f .(LIFT a) diff1 diff2 nf cf (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(LOWER a) diff1 diff2 nf cf (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(SHRINK a) diff1 diff2 nf cf (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
updCtxt2-renn name n m f .(upd name f) diff1 diff2 nf cf updCtxt2-upd with name ≟ n
... | yes p rewrite p = ⊥-elim (diff1 refl)
... | no p rewrite renn¬∈ n m (shiftUp 0 f) (→¬∈names-shiftUp {n} {0} {f} nf) = updCtxt2-upd


∈dom𝕎→¬s≡newChoiceT+ : (name : Name) (w : 𝕎·) (t : Term)
                         → name ∈ dom𝕎· w
                         → ¬ suc name ≡ newChoiceT+ w t
∈dom𝕎→¬s≡newChoiceT+ name w t i e rewrite suc-injective e = ¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names t)) i


¬0∈names-shiftNameUp : (t : Term) → ¬ 0 ∈ names (shiftNameUp 0 t)
¬0∈names-shiftNameUp t i rewrite names-shiftNameUp≡ 0 t with ∈-map⁻ (sucIf≤ 0) i
... | (y , j , e) = suc-≢-0 {y} (sym e)


choose-pres-getT≤ℕ : (cc : ContConds) (name name' : Name) (w : 𝕎·) (a : Term) (n : ℕ)
                      → ¬ name' ≡ name
                      → getT≤ℕ (chooseT name' w a) n name
                      → (getT≤ℕ w n name × getT≤ℕ (chooseT name' w a) n name)
choose-pres-getT≤ℕ cc name name' w a n diff g
  rewrite ContConds.ccGcd cc 0 name name' w a (λ x → diff (sym x))
  = g , g


choose-pres-∈names𝕎 : (cc : ContConds) (name name' : Name) (w : 𝕎·) (a : Term)
                       → ¬ name' ≡ name
                       → ¬ name ∈ names𝕎· w
                       → name ∈ dom𝕎· w
                       → (¬ name ∈ names𝕎· (chooseT name' w a)) × name ∈ dom𝕎· (chooseT name' w a)
choose-pres-∈names𝕎 cc name name' w a diff nnw idom =
  (λ x → nnw (ContConds.ccNchoosed cc name name' w a (λ z → diff (sym z)) x)) ,
  ContConds.ccDchoose cc name name' w a idom


-- This is similar to step-sat-isHighestℕ in continuity3.lagda.
-- updCtxt2's properties can essentially be copied from terms3b.lagda as this is almost the same definition.
-- We only need to prove that name's value increases, but for this only upd must update name.
-- So we
--   (1) require that ¬ name ∈ names f and
--   (2) that updCtxt2 name f (NAME name') only when ¬ name ≡ name'
step-sat-isHighestℕ2 : (cc : ContConds) (gc : get-choose-ℕ) {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
                       → compatible· name w1 Res⊤
                       → ∀𝕎-get0-NUM w1 name
                       → step a w1 ≡ just (b , w2)
                       → stepsPresHighestℕ2 name f b w2
                       → updCtxt2 name f a
                       → ¬ name ∈ names f -- This is so that (upd name f) does not update name when computing f
                       → ¬ name ∈ names𝕎· w1 -- This is so that reading choices does not bring name
                       → name ∈ dom𝕎· w1 -- this is so that FRESH does not pick name
                       → # f
                       → ΣhighestUpdCtxt2 name f n b w1 w2
step-sat-isHighestℕ2 cc gc {w1} {w2} {.NAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-NAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAT , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NAT
step-sat-isHighestℕ2 cc gc {w1} {w2} {.QNAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-QNAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QNAT , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QNAT
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QLT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QLT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QLT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(NUM x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NUM x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NUM _ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NUM _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b c d)} {x} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , c , w1 , refl , (λ x → x , x) , (nnw , idom) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , d , w1 , refl , (λ x → x , x) , (nnw , idom) , ctxt₃
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b c d)} {x} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf | inj₁ (k1 , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w1' , z) rewrite p | z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-IFLT₂ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt2 name f n b' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {b} {b'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-IFLT₂→ indb) ctxt₁ nnf nnw idom cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b c d)} {x} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-IFLT₁ ctxt₁ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-IFLT₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUC a ctxt) nnf nnw idom cf with is-NUM a
... | inj₁ (k1 , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , NUM (suc k1) , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NUM _
... | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-SUC₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-SUC₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PI a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PI a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PI _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LAMBDA a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LAMBDA a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LAMBDA _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf with is-LAM g
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl d
  where
    d : updCtxt2 name f t ⊎ t ≡ updBody name f
    d = updCtxt2-LAMBDA→ ctxt

    concl : updCtxt2 name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt2 name f n (sub a t) w1 w1
    concl (inj₁ u) = 0 , sub a t , w1 , refl , (λ s → s , s) , (nnw , idom) , updCtxt2-sub cf u ctxt₁
    concl (inj₂ u) rewrite u = c2
      where
        indb' : stepsPresHighestℕ2 name f (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f a cf = indb

        c1 : ΣhighestUpdCtxt2 name f n (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = →ΣhighestUpdCtxt2-upd cc gc {name} {f} {a} {w1} {n} compat wgt0 cf nnf nnw idom ctxt₁ indb'

        c2 : ΣhighestUpdCtxt2 name f n (sub a (updBody name f)) w1 w1
        c2 rewrite sub-upd name f a cf = c1
... | inj₂ x with is-CS g
... |    inj₁ (name' , p) rewrite p with is-NUM a
... |       inj₁ (m , q) rewrite q with getT⊎ m name' w1
... |          inj₁ (c , r) rewrite r | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , c , w1 , refl , (λ s → s , s) , (nnw , idom) , ¬∈names𝕎→updCtxt2 cc f name name' m c w1 r nnw
... |          inj₂ r rewrite r = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf | inj₂ x | inj₁ (name' , p) | inj₂ y with step⊎ a w1
... |          inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-APPLY₂ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-APPLY₂→ indb) ctxt₁ nnf nnw idom cf
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf | inj₂ x | inj₂ y with step⊎ g w1
... | inj₁ (g' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-APPLY₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n g' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {g} {g'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-APPLY₁→ indb) ctxt nnf nnw idom cf
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FIX a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FIX a ctxt) nnf nnw idom cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl d
  where
    d : updCtxt2 name f t ⊎ t ≡ updBody name f
    d = updCtxt2-LAMBDA→ ctxt

    concl : updCtxt2 name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt2 name f n (sub (FIX (LAMBDA t)) t) w1 w1
    concl (inj₁ u) = 0 , sub (FIX (LAMBDA t)) t , w1 , refl , (λ s → s , s) , (nnw , idom) , updCtxt2-sub cf u (updCtxt2-FIX _ ctxt)
    concl (inj₂ u) rewrite u = c2 --c2
      where
        indb' : stepsPresHighestℕ2 name f (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f (FIX (upd name f)) cf = indb

        c1 : ΣhighestUpdCtxt2 name f n (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = →ΣhighestUpdCtxt2-upd cc gc {name} {f} {FIX (upd name f)} {w1} {n} compat wgt0 cf nnf nnw idom (updCtxt2-FIX _ updCtxt2-upd) indb'

        c2 : ΣhighestUpdCtxt2 name f n (sub (FIX (upd name f)) (updBody name f)) w1 w1
        c2 rewrite sub-upd name f (FIX (upd name f)) cf = c1
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-FIX₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-FIX₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LET a b₁ ctxt ctxt₁) nnf nnw idom cf with isValue⊎ a
... | inj₁ x rewrite  sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub a b₁ , w1 , refl , (λ s → s , s) , (nnw , idom) , updCtxt2-sub cf ctxt₁ ctxt
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-LET₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-LET₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUM a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUM a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SUM _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PAIR a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PAIR a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PAIR _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SPREAD a b₁ ctxt ctxt₁) nnf nnw idom cf with is-PAIR a
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub v (sub u b₁) , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-sub cf (updCtxt2-sub cf ctxt₁ (updCtxt2-PAIR→₁ ctxt)) (updCtxt2-PAIR→₂ ctxt)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-SPREAD₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-SPREAD₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SET a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SET a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SET _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(ISECT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-ISECT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , ISECT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-ISECT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TUNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-UNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QTUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QTUNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QTUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(INL a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INL a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INL a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-INL _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(INR a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INR a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INR a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-INR _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub t b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-sub cf ctxt₁ (updCtxt2-INL→ ctxt)
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub t c , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-sub cf ctxt₂ (updCtxt2-INR→ ctxt)
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-DECIDE₁ ctxt₁ ctxt₂ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-DECIDE₁→ indb) ctxt nnf nnw idom cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , EQ a b₁ c , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-EQ _ _ _ ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ2 cc gc {w1} {w2} {.AX} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-AX nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , AX , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-AX
step-sat-isHighestℕ2 cc gc {w1} {w2} {.FREE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-FREE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FREE , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-FREE
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(CS name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CS name') nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , CS name' , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-CS _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(NAME name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NAME name' x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAME name' , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NAME _ x
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FRESH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FRESH a ctxt) nnf nnw idom cf
  rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
  = 0 , shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a) , startNewChoiceT Res⊤ w1 a ,
    refl , (λ x → gt' x , x) , (nnw' , idom') , upd1
  where
    gt' : getT≤ℕ (startNewChoiceT Res⊤ w1 a) n name → getT≤ℕ w1 n name
    gt' z rewrite ContConds.ccGstart cc name 0 Res⊤ a w1 idom = z

    nnw' : ¬ name ∈ names𝕎· (startNewChoiceT Res⊤ w1 a)
    nnw' = λ z → nnw (ContConds.ccNstart cc name w1 a z)

    idom' : name ∈ dom𝕎· (startNewChoiceT Res⊤ w1 a)
    idom' = ContConds.ccDstart cc name w1 a idom

    imp1 : (x : Name) →  x ∈ names (renn 0 (newChoiceT+ w1 a) a) → ¬ x ≡ 0
    imp1 x i z rewrite z = ⊥-elim (suc-≢-0 {newChoiceT w1 a} (sym (fst (∈names-renn-same {0} {newChoiceT+ w1 a} {a} i))))

    imp2 : 0 ∈ names (renn 0 (newChoiceT+ w1 a) a) → 0 < 0
    imp2 z = ⊥-elim (suc-≢-0 {newChoiceT w1 a} (sym (fst (∈names-renn-same {0} {newChoiceT+ w1 a} {a} z))))

    upd3 : updCtxt2 (suc name) (shiftNameUp 0 f) (renn 0 (newChoiceT+ w1 a) a)
    upd3 = updCtxt2-renn (suc name) 0 (newChoiceT+ w1 a) (shiftNameUp 0 f) a (suc-≢-0 {name}) (∈dom𝕎→¬s≡newChoiceT+ name w1 a idom) (¬0∈names-shiftNameUp f) (→#shiftNameUp 0 {f} cf) ctxt

    upd2 : updCtxt2 (sucIf≤ 0 name) (shiftNameUp 0 f) (renn 0 (newChoiceT+ w1 a) a)
    upd2 rewrite sym (suc≡sucIf≤0 name) = upd3

    upd1 : updCtxt2 name f (shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a))
    upd1 = →updCtxt2-shiftNameDown 0 {name} {f} cf {renn 0 (newChoiceT+ w1 a) a} imp1 imp2 upd2
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CHOOSE a b₁ ctxt ctxt₁) nnf nnw idom cf with is-NAME a
... | inj₁ (nm , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , AX , chooseT nm w1 b₁ , refl ,
  choose-pres-getT≤ℕ cc name nm w1 b₁ n (updCtxt2-NAME→ ctxt) ,
  choose-pres-∈names𝕎 cc name nm w1 b₁ (updCtxt2-NAME→ ctxt) nnw idom ,
  updCtxt2-AX
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-CHOOSE₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-CHOOSE₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TSQUASH a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TSQUASH a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TSQUASH _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TTRUNC a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TTRUNC a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TTRUNC _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TCONST a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TCONST a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TCONST _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUBSING a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUBSING a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SUBSING _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.PURE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-PURE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PURE , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PURE
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(DUM a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DUM a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , DUM a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-DUM _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FFDEFS a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FFDEFS a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-FFDEFS _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNIV x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNIV _ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-UNIV _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LIFT a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LIFT a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LIFT _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LOWER a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LOWER a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LOWER _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SHRINK a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SHRINK a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SHRINK _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(upd name f)} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-upd nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , upd name f , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-upd

\end{code}
