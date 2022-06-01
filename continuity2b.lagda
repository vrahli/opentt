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
  → (getT≤ℕ w2 n name --getT 0 name w2 ≡ just (NUM n)
      → isHighestℕ {k} {w1} {w2} {a} {b} n name comp)
     × pres∈names𝕎 {k} {w1} {w2} {a} {b} name comp


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
           × pres∈names𝕎 {k1} {w1} {w1'} {b} {NUM m} name comp1b
    ind' = ind k1 (<⇒≤ ltk1) {w1} {w1'} {b} {NUM m} {n} comp1b tt nnb compat wgt0

    j : getT≤ℕ (chooseT0if name w1' m' m) n name
         → (getT≤ℕ w1 n name × isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} n name comp2)
    j g = isHighestℕ→getT≤ℕ {k1} {w1} {w1'} {b} {NUM m} n name comp1b (fst ind' g') , j1
      where
        g' : getT≤ℕ w1' n name
        g' = getT≤ℕ-chooseT0if→ gc {w1'} {name} {n} {m} {m'} (⊑-compatible· e1 compat) gt0 g

        j1 : isHighestℕ {k2} {w1} {chooseT0if name w1' m' m} {LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} n name comp2
        j1 = →isHighestℕ-upd-body2 cc gc {k1} {k2} {name} {w1} {w1'} {b} {f} {n} {m} {m'} cf nnf nnw idom compat comp1b comp2 gt0 g (fst ind' g') (snd ind' nnw idom)

    inw : ∈names𝕎 {k2} {w1} {chooseT0if name w1' m' m} name comp2
    inw = →isHighestℕ-upd-body2-∈names𝕎 cc gc {k1} {k2} {name} {w1} {w1'} {b} {f} {m} {m'} cf nnf nnw idom comp1b comp2 gt0 (snd ind' nnw idom)



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
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUC a ctxt) nnf nnw idom cf = {!!}
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
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FIX a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FIX a ctxt) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LET a b₁ ctxt ctxt₁) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUM a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUM a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SUM _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PAIR a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PAIR a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PAIR _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SPREAD a b₁ ctxt ctxt₁) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SET a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SET a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SET _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(ISECT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-ISECT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , ISECT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-ISECT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TUNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-UNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QTUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QTUNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QTUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(INL a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INL a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INL a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-INL _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(INR a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INR a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INR a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-INR _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , EQ a b₁ c , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-EQ _ _ _ ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ2 cc gc {w1} {w2} {.AX} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-AX nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , AX , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-AX
step-sat-isHighestℕ2 cc gc {w1} {w2} {.FREE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-FREE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FREE , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-FREE
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(CS name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CS name') nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , CS name' , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-CS _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(NAME name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NAME name' x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAME name' , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NAME _ x
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FRESH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FRESH a ctxt) nnf nnw idom cf
  rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
  = 0 , shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a) , startNewChoiceT Res⊤ w1 a ,
    refl , (λ x → gt' x , x) , (nnw' , idom') , {!!}
  where
    gt' : getT≤ℕ (startNewChoiceT Res⊤ w1 a) n name → getT≤ℕ w1 n name
    gt' z rewrite ContConds.ccGstart cc name 0 Res⊤ a w1 idom = z

    nnw' : ¬ name ∈ names𝕎· (startNewChoiceT Res⊤ w1 a)
    nnw' = λ z → nnw (ContConds.ccNstart cc name w1 a z)

    idom' : name ∈ dom𝕎· (startNewChoiceT Res⊤ w1 a)
    idom' = ContConds.ccDstart cc name w1 a idom
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CHOOSE a b₁ ctxt ctxt₁) nnf nnw idom cf = {!!}
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
