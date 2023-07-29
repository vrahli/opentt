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


module continuity2b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import encodeDef(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)



data updCtxt2 (name : Name) (f : Term) : Term → Set where
  updCtxt2-VAR     : (x : Var) → updCtxt2 name f (VAR x)
--  updCtxt2-NAT     : updCtxt2 name f NAT
  updCtxt2-QNAT    : updCtxt2 name f QNAT
--  updCtxt2-TNAT    : updCtxt2 name f TNAT
  updCtxt2-LT      : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (LT a b)
  updCtxt2-QLT     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (QLT a b)
  updCtxt2-NUM     : (x : ℕ) → updCtxt2 name f (NUM x)
  updCtxt2-IFLT    : (a b c d : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f d → updCtxt2 name f (IFLT a b c d)
  updCtxt2-IFEQ    : (a b c d : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f d → updCtxt2 name f (IFEQ a b c d)
  updCtxt2-SUC     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SUC a)
  updCtxt2-NATREC  : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (NATREC a b c)
  updCtxt2-PI      : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (PI a b)
  updCtxt2-LAMBDA  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LAMBDA a)
  updCtxt2-MSEQ    : (s : 𝕊) → updCtxt2 name f (MSEQ s)
  updCtxt2-MAPP    : (s : 𝕊) (a : Term) → updCtxt2 name f a → updCtxt2 name f (MAPP s a)
  updCtxt2-APPLY   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (APPLY a b)
  updCtxt2-FIX     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (FIX a)
  updCtxt2-LET     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (LET a b)
  updCtxt2-SUM     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SUM a b)
  updCtxt2-PAIR    : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (PAIR a b)
  updCtxt2-SPREAD  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SPREAD a b)
  updCtxt2-WT      : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (WT a b c)
  updCtxt2-SUP     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SUP a b)
  updCtxt2-WREC    : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (WREC a b)
  updCtxt2-MT      : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (MT a b c)
  updCtxt2-SET     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SET a b)
  updCtxt2-ISECT   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (ISECT a b)
  updCtxt2-TUNION  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (TUNION a b)
  updCtxt2-UNION   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (UNION a b)
--  updCtxt2-QTUNION : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (QTUNION a b)
  updCtxt2-INL     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (INL a)
  updCtxt2-INR     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (INR a)
  updCtxt2-DECIDE  : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (DECIDE a b c)
  updCtxt2-EQ      : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (EQ a b c)
--  updCtxt2-EQB     : (a b c d : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f d → updCtxt2 name f (EQB a b c d)
  updCtxt2-AX      : updCtxt2 name f AX
  updCtxt2-FREE    : updCtxt2 name f FREE
  updCtxt2-CS      : (name' : Name) → updCtxt2 name f (CS name')
  updCtxt2-NAME    : (name' : Name) → ¬ name' ≡ name → updCtxt2 name f (NAME name')
  updCtxt2-FRESH   : (a : Term) → updCtxt2 (suc name) (shiftNameUp 0 f) a → updCtxt2 name f (FRESH a)
  updCtxt2-LOAD    : (a : Term) → updCtxt2 name f (LOAD a)
  updCtxt2-CHOOSE  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (CHOOSE a b)
--  updCtxt2-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updCtxt2 name1 name2 f a₁ a₂ → updCtxt2 name1 name2 f b₁ b₂ → updCtxt2 name1 name2 f c₁ c₂ → updCtxt2 name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
--  updCtxt2-TSQUASH : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TSQUASH a)
--  updCtxt2-TTRUNC  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TTRUNC a)
  updCtxt2-NOWRITE : updCtxt2 name f NOWRITE
  updCtxt2-NOREAD  : updCtxt2 name f NOREAD
  updCtxt2-SUBSING : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SUBSING a)
  updCtxt2-PURE    : updCtxt2 name f PURE
  updCtxt2-NOSEQ   : updCtxt2 name f NOSEQ
  updCtxt2-NOENC   : updCtxt2 name f NOENC
  updCtxt2-TERM    : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TERM a)
  updCtxt2-ENC     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (ENC a)
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



abstract

  →updCtxt2-shiftUp : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                       → updCtxt2 name f a
                       → updCtxt2 name f (shiftUp v a)
  →updCtxt2-shiftUp v {name} {f} cf {.(VAR x)} (updCtxt2-VAR x) = updCtxt2-VAR _
--  →updCtxt2-shiftUp v {name} {f} cf {.NAT} updCtxt2-NAT = updCtxt2-NAT
  →updCtxt2-shiftUp v {name} {f} cf {.QNAT} updCtxt2-QNAT = updCtxt2-QNAT
--  →updCtxt2-shiftUp v {name} {f} cf {.TNAT} updCtxt2-TNAT = updCtxt2-TNAT
  →updCtxt2-shiftUp v {name} {f} cf {.(LT a b)} (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(QLT a b)} (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(NUM x)} (updCtxt2-NUM x) = updCtxt2-NUM _
  →updCtxt2-shiftUp v {name} {f} cf {.(IFLT a b c d)} (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃) (→updCtxt2-shiftUp v cf upd₄)
  →updCtxt2-shiftUp v {name} {f} cf {.(IFEQ a b c d)} (updCtxt2-IFEQ a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFEQ _ _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃) (→updCtxt2-shiftUp v cf upd₄)
  →updCtxt2-shiftUp v {name} {f} cf {.(SUC a)} (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(NATREC a b c)} (updCtxt2-NATREC a b c upd₁ upd₂ upd₃) = updCtxt2-NATREC _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃)
  →updCtxt2-shiftUp v {name} {f} cf {.(PI a b)} (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(LAMBDA a)} (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (→updCtxt2-shiftUp (suc v) cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(MSEQ s)} (updCtxt2-MSEQ s) = updCtxt2-MSEQ _
  →updCtxt2-shiftUp v {name} {f} cf {.(MAPP s a)} (updCtxt2-MAPP s a upd₁) = updCtxt2-MAPP _ _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(APPLY a b)} (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(FIX a)} (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(LET a b)} (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(SUM a b)} (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(PAIR a b)} (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(SPREAD a b)} (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc (suc v)) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(WT a b c)} (updCtxt2-WT a b c upd₁ upd₂ upd₃) = updCtxt2-WT _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂) (→updCtxt2-shiftUp v cf upd₃)
  →updCtxt2-shiftUp v {name} {f} cf {.(SUP a b)} (updCtxt2-SUP a b upd₁ upd₂) = updCtxt2-SUP _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(WREC a b)} (updCtxt2-WREC a b upd₁ upd₂) = updCtxt2-WREC _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc (suc (suc v))) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(MT a b c)} (updCtxt2-MT a b c upd₁ upd₂ upd₃) = updCtxt2-MT _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂) (→updCtxt2-shiftUp v cf upd₃)
  →updCtxt2-shiftUp v {name} {f} cf {.(SET a b)} (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(ISECT a b)} (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(TUNION a b)} (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(UNION a b)} (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
--  →updCtxt2-shiftUp v {name} {f} cf {.(QTUNION a b)} (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(INL a)} (updCtxt2-INL a upd₁) = updCtxt2-INL _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(INR a)} (updCtxt2-INR a upd₁) = updCtxt2-INR _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(DECIDE a b c)} (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp (suc v) cf upd₂) (→updCtxt2-shiftUp (suc v) cf upd₃)
  →updCtxt2-shiftUp v {name} {f} cf {.(EQ a b c)} (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃)
--  →updCtxt2-shiftUp v {name} {f} cf {.(EQB a b c d)} (updCtxt2-EQB a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-EQB _ _ _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂) (→updCtxt2-shiftUp v cf upd₃) (→updCtxt2-shiftUp v cf upd₄)
  →updCtxt2-shiftUp v {name} {f} cf {.AX} updCtxt2-AX = updCtxt2-AX
  →updCtxt2-shiftUp v {name} {f} cf {.FREE} updCtxt2-FREE = updCtxt2-FREE
  →updCtxt2-shiftUp v {name} {f} cf {.(CS name')} (updCtxt2-CS name') = updCtxt2-CS _
  →updCtxt2-shiftUp v {name} {f} cf {.(NAME name')} (updCtxt2-NAME name' x) = updCtxt2-NAME _ x
  →updCtxt2-shiftUp v {name} {f} cf {.(FRESH a)} (updCtxt2-FRESH a upd₁) = updCtxt2-FRESH _ (→updCtxt2-shiftUp v (→#shiftNameUp 0 {f} cf) upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(LOAD a)} (updCtxt2-LOAD a) = updCtxt2-LOAD _ --upd₁ --updCtxt2-LOAD _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(CHOOSE a b)} (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
--  →updCtxt2-shiftUp v {name} {f} cf {.(TSQUASH a)} (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (→updCtxt2-shiftUp v cf upd₁)
--  →updCtxt2-shiftUp v {name} {f} cf {.(TTRUNC a)} (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.NOWRITE} updCtxt2-NOWRITE = updCtxt2-NOWRITE
  →updCtxt2-shiftUp v {name} {f} cf {.NOREAD}  updCtxt2-NOREAD  = updCtxt2-NOREAD
  →updCtxt2-shiftUp v {name} {f} cf {.(SUBSING a)} (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.PURE} updCtxt2-PURE = updCtxt2-PURE
  →updCtxt2-shiftUp v {name} {f} cf {.NOSEQ} updCtxt2-NOSEQ = updCtxt2-NOSEQ
  →updCtxt2-shiftUp v {name} {f} cf {.NOENC} updCtxt2-NOENC = updCtxt2-NOENC
  →updCtxt2-shiftUp v {name} {f} cf {.(TERM a)} (updCtxt2-TERM a upd₁) = updCtxt2-TERM _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(ENC a)} (updCtxt2-ENC a upd₁) = updCtxt2-ENC _ upd₁
  →updCtxt2-shiftUp v {name} {f} cf {.(DUM a)} (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(FFDEFS a b)} (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (→updCtxt2-shiftUp v cf upd₁) (→updCtxt2-shiftUp v cf upd₂)
  →updCtxt2-shiftUp v {name} {f} cf {.(UNIV x)} (updCtxt2-UNIV x) = updCtxt2-UNIV _
  →updCtxt2-shiftUp v {name} {f} cf {.(LIFT a)} (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(LOWER a)} (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(SHRINK a)} (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (→updCtxt2-shiftUp v cf upd₁)
  →updCtxt2-shiftUp v {name} {f} cf {.(upd name f)} updCtxt2-upd
    rewrite sucIf≤s0 v | #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updCtxt2-upd



abstract

  →updCtxt2-shiftDown : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                         → updCtxt2 name f a
                         → updCtxt2 name f (shiftDown v a)
  →updCtxt2-shiftDown v {name} {f} cf {.(VAR x)} (updCtxt2-VAR x) = updCtxt2-VAR _
--  →updCtxt2-shiftDown v {name} {f} cf {.NAT} updCtxt2-NAT = updCtxt2-NAT
  →updCtxt2-shiftDown v {name} {f} cf {.QNAT} updCtxt2-QNAT = updCtxt2-QNAT
--  →updCtxt2-shiftDown v {name} {f} cf {.TNAT} updCtxt2-TNAT = updCtxt2-TNAT
  →updCtxt2-shiftDown v {name} {f} cf {.(LT a b)} (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(QLT a b)} (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(NUM x)} (updCtxt2-NUM x) = updCtxt2-NUM _
  →updCtxt2-shiftDown v {name} {f} cf {.(IFLT a b c d)} (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃) (→updCtxt2-shiftDown v cf upd₄)
  →updCtxt2-shiftDown v {name} {f} cf {.(IFEQ a b c d)} (updCtxt2-IFEQ a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFEQ _ _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃) (→updCtxt2-shiftDown v cf upd₄)
  →updCtxt2-shiftDown v {name} {f} cf {.(SUC a)} (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(NATREC a b c)} (updCtxt2-NATREC a b c upd₁ upd₂ upd₃) = updCtxt2-NATREC _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃)
  →updCtxt2-shiftDown v {name} {f} cf {.(PI a b)} (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(LAMBDA a)} (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (→updCtxt2-shiftDown (suc v) cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(MSEQ s)} (updCtxt2-MSEQ s) = updCtxt2-MSEQ _
  →updCtxt2-shiftDown v {name} {f} cf {.(MAPP s a)} (updCtxt2-MAPP s a upd₁) = updCtxt2-MAPP _ _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(APPLY a b)} (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(FIX a)} (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(LET a b)} (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(SUM a b)} (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(PAIR a b)} (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(SPREAD a b)} (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc (suc v)) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(WT a b c)} (updCtxt2-WT a b c upd₁ upd₂ upd₃) = updCtxt2-WT _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂) (→updCtxt2-shiftDown v cf upd₃)
  →updCtxt2-shiftDown v {name} {f} cf {.(SUP a b)} (updCtxt2-SUP a b upd₁ upd₂) = updCtxt2-SUP _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(WREC a b)} (updCtxt2-WREC a b upd₁ upd₂) = updCtxt2-WREC _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc (suc (suc v))) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(MT a b c)} (updCtxt2-MT a b c upd₁ upd₂ upd₃) = updCtxt2-MT _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂) (→updCtxt2-shiftDown v cf upd₃)
  →updCtxt2-shiftDown v {name} {f} cf {.(SET a b)} (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(ISECT a b)} (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(TUNION a b)} (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(UNION a b)} (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
--  →updCtxt2-shiftDown v {name} {f} cf {.(QTUNION a b)} (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(INL a)} (updCtxt2-INL a upd₁) = updCtxt2-INL _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(INR a)} (updCtxt2-INR a upd₁) = updCtxt2-INR _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(DECIDE a b c)} (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown (suc v) cf upd₂) (→updCtxt2-shiftDown (suc v) cf upd₃)
  →updCtxt2-shiftDown v {name} {f} cf {.(EQ a b c)} (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃)
--  →updCtxt2-shiftDown v {name} {f} cf {.(EQB a b c d)} (updCtxt2-EQB a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-EQB _ _ _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂) (→updCtxt2-shiftDown v cf upd₃) (→updCtxt2-shiftDown v cf upd₄)
  →updCtxt2-shiftDown v {name} {f} cf {.AX} updCtxt2-AX = updCtxt2-AX
  →updCtxt2-shiftDown v {name} {f} cf {.FREE} updCtxt2-FREE = updCtxt2-FREE
  →updCtxt2-shiftDown v {name} {f} cf {.(CS name')} (updCtxt2-CS name') = updCtxt2-CS _
  →updCtxt2-shiftDown v {name} {f} cf {.(NAME name')} (updCtxt2-NAME name' x) = updCtxt2-NAME _ x
  →updCtxt2-shiftDown v {name} {f} cf {.(FRESH a)} (updCtxt2-FRESH a upd₁) = updCtxt2-FRESH _ (→updCtxt2-shiftDown v (→#shiftNameUp 0 {f} cf) upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(LOAD a)} (updCtxt2-LOAD a) = updCtxt2-LOAD _ --upd₁ --updCtxt2-LOAD _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(CHOOSE a b)} (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
--  →updCtxt2-shiftDown v {name} {f} cf {.(TSQUASH a)} (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (→updCtxt2-shiftDown v cf upd₁)
--  →updCtxt2-shiftDown v {name} {f} cf {.(TTRUNC a)} (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.NOWRITE} updCtxt2-NOWRITE = updCtxt2-NOWRITE
  →updCtxt2-shiftDown v {name} {f} cf {.NOREAD}  updCtxt2-NOREAD  = updCtxt2-NOREAD
  →updCtxt2-shiftDown v {name} {f} cf {.(SUBSING a)} (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.PURE} updCtxt2-PURE = updCtxt2-PURE
  →updCtxt2-shiftDown v {name} {f} cf {.NOSEQ} updCtxt2-NOSEQ = updCtxt2-NOSEQ
  →updCtxt2-shiftDown v {name} {f} cf {.NOENC} updCtxt2-NOENC = updCtxt2-NOENC
  →updCtxt2-shiftDown v {name} {f} cf {.(TERM a)} (updCtxt2-TERM a upd₁) = updCtxt2-TERM _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(ENC a)} (updCtxt2-ENC a upd₁) = updCtxt2-ENC _ upd₁
  →updCtxt2-shiftDown v {name} {f} cf {.(DUM a)} (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(FFDEFS a b)} (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (→updCtxt2-shiftDown v cf upd₁) (→updCtxt2-shiftDown v cf upd₂)
  →updCtxt2-shiftDown v {name} {f} cf {.(UNIV x)} (updCtxt2-UNIV x) = updCtxt2-UNIV _
  →updCtxt2-shiftDown v {name} {f} cf {.(LIFT a)} (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(LOWER a)} (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(SHRINK a)} (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (→updCtxt2-shiftDown v cf upd₁)
  →updCtxt2-shiftDown v {name} {f} cf {.(upd name f)} updCtxt2-upd
    rewrite sucIf≤s0 v | #shiftDown (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updCtxt2-upd



abstract

  →updCtxt2-shiftNameUp : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                           → updCtxt2 name f a
                           → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(VAR x)} (updCtxt2-VAR x) = updCtxt2-VAR _
--  →updCtxt2-shiftNameUp v {name} {f} cf {.NAT} updCtxt2-NAT = updCtxt2-NAT
  →updCtxt2-shiftNameUp v {name} {f} cf {.QNAT} updCtxt2-QNAT = updCtxt2-QNAT
--  →updCtxt2-shiftNameUp v {name} {f} cf {.TNAT} updCtxt2-TNAT = updCtxt2-TNAT
  →updCtxt2-shiftNameUp v {name} {f} cf {.(LT a b)} (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(QLT a b)} (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(NUM x)} (updCtxt2-NUM x) = updCtxt2-NUM _
  →updCtxt2-shiftNameUp v {name} {f} cf {.(IFLT a b c d)} (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃) (→updCtxt2-shiftNameUp v cf upd₄)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(IFEQ a b c d)} (updCtxt2-IFEQ a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFEQ _ _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃) (→updCtxt2-shiftNameUp v cf upd₄)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(SUC a)} (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(NATREC a b c)} (updCtxt2-NATREC a b c upd₁ upd₂ upd₃) = updCtxt2-NATREC _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(PI a b)} (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(LAMBDA a)} (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(MSEQ s)} (updCtxt2-MSEQ s) = updCtxt2-MSEQ _
  →updCtxt2-shiftNameUp v {name} {f} cf {.(MAPP s a)} (updCtxt2-MAPP s a upd₁) = updCtxt2-MAPP _ _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(APPLY a b)} (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(FIX a)} (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(LET a b)} (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(SUM a b)} (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(PAIR a b)} (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(SPREAD a b)} (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(WT a b c)} (updCtxt2-WT a b c upd₁ upd₂ upd₃) = updCtxt2-WT _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(SUP a b)} (updCtxt2-SUP a b upd₁ upd₂) = updCtxt2-SUP _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(WREC a b)} (updCtxt2-WREC a b upd₁ upd₂) = updCtxt2-WREC _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(MT a b c)} (updCtxt2-MT a b c upd₁ upd₂ upd₃) = updCtxt2-MT _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(SET a b)} (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(ISECT a b)} (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(TUNION a b)} (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(UNION a b)} (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
--  →updCtxt2-shiftNameUp v {name} {f} cf {.(QTUNION a b)} (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(INL a)} (updCtxt2-INL a upd₁) = updCtxt2-INL _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(INR a)} (updCtxt2-INR a upd₁) = updCtxt2-INR _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(DECIDE a b c)} (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(EQ a b c)} (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃)
--  →updCtxt2-shiftNameUp v {name} {f} cf {.(EQB a b c d)} (updCtxt2-EQB a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-EQB _ _ _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂) (→updCtxt2-shiftNameUp v cf upd₃) (→updCtxt2-shiftNameUp v cf upd₄)
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
  →updCtxt2-shiftNameUp v {name} {f} cf {.(LOAD a)} (updCtxt2-LOAD a) = updCtxt2-LOAD _ --(→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(CHOOSE a b)} (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (→updCtxt2-shiftNameUp v cf upd₁) (→updCtxt2-shiftNameUp v cf upd₂)
--  →updCtxt2-shiftNameUp v {name} {f} cf {.(TSQUASH a)} (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (→updCtxt2-shiftNameUp v cf upd₁)
--  →updCtxt2-shiftNameUp v {name} {f} cf {.(TTRUNC a)} (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.NOWRITE} updCtxt2-NOWRITE = updCtxt2-NOWRITE
  →updCtxt2-shiftNameUp v {name} {f} cf {.NOREAD}  updCtxt2-NOREAD  = updCtxt2-NOREAD
  →updCtxt2-shiftNameUp v {name} {f} cf {.(SUBSING a)} (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.PURE} updCtxt2-PURE = updCtxt2-PURE
  →updCtxt2-shiftNameUp v {name} {f} cf {.NOSEQ} updCtxt2-NOSEQ = updCtxt2-NOSEQ
  →updCtxt2-shiftNameUp v {name} {f} cf {.NOENC} updCtxt2-NOENC = updCtxt2-NOENC
  →updCtxt2-shiftNameUp v {name} {f} cf {.(TERM a)} (updCtxt2-TERM a upd₁) = updCtxt2-TERM _ (→updCtxt2-shiftNameUp v cf upd₁)
  →updCtxt2-shiftNameUp v {name} {f} cf {.(ENC a)} (updCtxt2-ENC a upd₁) = updCtxt2-ENC _ (→updCtxt2-shiftNameUp v cf upd₁)
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



abstract

  updCtxt2-subv : {name : Name} {f : Term} (cf : # f) (v : Var) {a b : Term}
                  → updCtxt2 name f a
                  → updCtxt2 name f b
                  → updCtxt2 name f (subv v b a)
  updCtxt2-subv {name} {f} cf v {.(VAR x)} {b} (updCtxt2-VAR x) updb with x ≟ v
  ... | yes p = updb
  ... | no p = updCtxt2-VAR _
--  updCtxt2-subv {name} {f} cf v {.NAT} {b} updCtxt2-NAT updb = updCtxt2-NAT
  updCtxt2-subv {name} {f} cf v {.QNAT} {b} updCtxt2-QNAT updb = updCtxt2-QNAT
--  updCtxt2-subv {name} {f} cf v {.TNAT} {b} updCtxt2-TNAT updb = updCtxt2-TNAT
  updCtxt2-subv {name} {f} cf v {.(LT a b₁)} {b} (updCtxt2-LT a b₁ upda upda₁) updb = updCtxt2-LT _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(QLT a b₁)} {b} (updCtxt2-QLT a b₁ upda upda₁) updb = updCtxt2-QLT _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(NUM x)} {b} (updCtxt2-NUM x) updb = updCtxt2-NUM _
  updCtxt2-subv {name} {f} cf v {.(IFLT a b₁ c d)} {b} (updCtxt2-IFLT a b₁ c d upda upda₁ upda₂ upda₃) updb = updCtxt2-IFLT _ _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb) (updCtxt2-subv cf v upda₃ updb)
  updCtxt2-subv {name} {f} cf v {.(IFEQ a b₁ c d)} {b} (updCtxt2-IFEQ a b₁ c d upda upda₁ upda₂ upda₃) updb = updCtxt2-IFEQ _ _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb) (updCtxt2-subv cf v upda₃ updb)
  updCtxt2-subv {name} {f} cf v {.(SUC a)} {b} (updCtxt2-SUC a upda) updb = updCtxt2-SUC _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(NATREC a a₁ a₂)} {b} (updCtxt2-NATREC a a₁ a₂ upda upda₁ upda₂) updb = updCtxt2-NATREC _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb)
  updCtxt2-subv {name} {f} cf v {.(PI a b₁)} {b} (updCtxt2-PI a b₁ upda upda₁) updb = updCtxt2-PI _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(LAMBDA a)} {b} (updCtxt2-LAMBDA a upda) updb = updCtxt2-LAMBDA _ (updCtxt2-subv cf (suc v) upda (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(MSEQ s)} {b} (updCtxt2-MSEQ s) updb = updCtxt2-MSEQ _
  updCtxt2-subv {name} {f} cf v {.(MAPP s a)} {b} (updCtxt2-MAPP s a upda) updb = updCtxt2-MAPP _ _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(APPLY a b₁)} {b} (updCtxt2-APPLY a b₁ upda upda₁) updb = updCtxt2-APPLY _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(FIX a)} {b} (updCtxt2-FIX a upda) updb = updCtxt2-FIX _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(LET a b₁)} {b} (updCtxt2-LET a b₁ upda upda₁) updb = updCtxt2-LET _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(SUM a b₁)} {b} (updCtxt2-SUM a b₁ upda upda₁) updb = updCtxt2-SUM _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(PAIR a b₁)} {b} (updCtxt2-PAIR a b₁ upda upda₁) updb = updCtxt2-PAIR _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(SPREAD a b₁)} {b} (updCtxt2-SPREAD a b₁ upda upda₁) updb = updCtxt2-SPREAD _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc (suc v)) upda₁ (→updCtxt2-shiftUp 0 cf (→updCtxt2-shiftUp 0 cf updb)))
  updCtxt2-subv {name} {f} cf v {.(WT a b₁ c)} {b} (updCtxt2-WT a b₁ c upda upda₁ upda₂) updb = updCtxt2-WT _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb)) (updCtxt2-subv cf v upda₂ updb)
  updCtxt2-subv {name} {f} cf v {.(SUP a b₁)} {b} (updCtxt2-SUP a b₁ upda upda₁) updb = updCtxt2-SUP _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(WREC a b₁)} {b} (updCtxt2-WREC a b₁ upda upda₁) updb = updCtxt2-WREC _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc (suc (suc v))) upda₁ (→updCtxt2-shiftUp 0 cf (→updCtxt2-shiftUp 0 cf (→updCtxt2-shiftUp 0 cf updb))))
  updCtxt2-subv {name} {f} cf v {.(MT a b₁ c)} {b} (updCtxt2-MT a b₁ c upda upda₁ upda₂) updb = updCtxt2-MT _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb)) (updCtxt2-subv cf v upda₂ updb)
  updCtxt2-subv {name} {f} cf v {.(SET a b₁)} {b} (updCtxt2-SET a b₁ upda upda₁) updb = updCtxt2-SET _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(ISECT a b₁)} {b} (updCtxt2-ISECT a b₁ upda upda₁) updb = updCtxt2-ISECT _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(TUNION a b₁)} {b} (updCtxt2-TUNION a b₁ upda upda₁) updb = updCtxt2-TUNION _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(UNION a b₁)} {b} (updCtxt2-UNION a b₁ upda upda₁) updb = updCtxt2-UNION _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
--  updCtxt2-subv {name} {f} cf v {.(QTUNION a b₁)} {b} (updCtxt2-QTUNION a b₁ upda upda₁) updb = updCtxt2-QTUNION _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
  updCtxt2-subv {name} {f} cf v {.(INL a)} {b} (updCtxt2-INL a upda) updb = updCtxt2-INL _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(INR a)} {b} (updCtxt2-INR a upda) updb = updCtxt2-INR _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(DECIDE a b₁ c)} {b} (updCtxt2-DECIDE a b₁ c upda upda₁ upda₂) updb = updCtxt2-DECIDE _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf (suc v) upda₁ (→updCtxt2-shiftUp 0 cf updb)) (updCtxt2-subv cf (suc v) upda₂ (→updCtxt2-shiftUp 0 cf updb))
  updCtxt2-subv {name} {f} cf v {.(EQ a b₁ c)} {b} (updCtxt2-EQ a b₁ c upda upda₁ upda₂) updb = updCtxt2-EQ _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb)
--  updCtxt2-subv {name} {f} cf v {.(EQB a b₁ c d)} {b} (updCtxt2-EQB a b₁ c d upda upda₁ upda₂ upda₃) updb = updCtxt2-EQB _ _ _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb) (updCtxt2-subv cf v upda₂ updb) (updCtxt2-subv cf v upda₃ updb)
  updCtxt2-subv {name} {f} cf v {.AX} {b} updCtxt2-AX updb = updCtxt2-AX
  updCtxt2-subv {name} {f} cf v {.FREE} {b} updCtxt2-FREE updb = updCtxt2-FREE
  updCtxt2-subv {name} {f} cf v {.(CS name')} {b} (updCtxt2-CS name') updb = updCtxt2-CS _
  updCtxt2-subv {name} {f} cf v {.(NAME name')} {b} (updCtxt2-NAME name' x) updb = updCtxt2-NAME _ x
  updCtxt2-subv {name} {f} cf v {.(FRESH a)} {b} (updCtxt2-FRESH a upda) updb = updCtxt2-FRESH _ (updCtxt2-subv (→#shiftNameUp 0 {f} cf) v upda (→updCtxt2-shiftNameUp0 {name} cf updb))
  updCtxt2-subv {name} {f} cf v {.(LOAD a)} {b} (updCtxt2-LOAD a) updb = updCtxt2-LOAD _ --upda --updCtxt2-LOAD _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(CHOOSE a b₁)} {b} (updCtxt2-CHOOSE a b₁ upda upda₁) updb = updCtxt2-CHOOSE _ _ (updCtxt2-subv cf v upda updb) (updCtxt2-subv cf v upda₁ updb)
--  updCtxt2-subv {name} {f} cf v {.(TSQUASH a)} {b} (updCtxt2-TSQUASH a upda) updb = updCtxt2-TSQUASH _ (updCtxt2-subv cf v upda updb)
--  updCtxt2-subv {name} {f} cf v {.(TTRUNC a)} {b} (updCtxt2-TTRUNC a upda) updb = updCtxt2-TTRUNC _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.NOWRITE} {b} updCtxt2-NOWRITE updb = updCtxt2-NOWRITE
  updCtxt2-subv {name} {f} cf v {.NOREAD}  {b} updCtxt2-NOREAD  updb = updCtxt2-NOREAD
  updCtxt2-subv {name} {f} cf v {.(SUBSING a)} {b} (updCtxt2-SUBSING a upda) updb = updCtxt2-SUBSING _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.PURE} {b} updCtxt2-PURE updb = updCtxt2-PURE
  updCtxt2-subv {name} {f} cf v {.NOSEQ} {b} updCtxt2-NOSEQ updb = updCtxt2-NOSEQ
  updCtxt2-subv {name} {f} cf v {.NOENC} {b} updCtxt2-NOENC updb = updCtxt2-NOENC
  updCtxt2-subv {name} {f} cf v {.(TERM a)} {b} (updCtxt2-TERM a upda) updb = updCtxt2-TERM _ (updCtxt2-subv cf v upda updb)
  updCtxt2-subv {name} {f} cf v {.(ENC a)} {b} (updCtxt2-ENC a upda) updb = updCtxt2-ENC _ upda
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



updCtxt2-SUP→₁ : {name : Name} {f a b : Term}
                   → updCtxt2 name f (SUP a b)
                   → updCtxt2 name f a
updCtxt2-SUP→₁ {name} {f} {a} {b} (updCtxt2-SUP .a .b ca cb) = ca



updCtxt2-SUP→₂ : {name : Name} {f a b : Term}
                   → updCtxt2 name f (SUP a b)
                   → updCtxt2 name f b
updCtxt2-SUP→₂ {name} {f} {a} {b} (updCtxt2-SUP .a .b ca cb) = cb



updCtxt2-INL→ : {name : Name} {f a : Term}
                   → updCtxt2 name f (INL a)
                   → updCtxt2 name f a
updCtxt2-INL→ {name} {f} {a} (updCtxt2-INL .a ca) = ca



updCtxt2-INR→ : {name : Name} {f a : Term}
                   → updCtxt2 name f (INR a)
                   → updCtxt2 name f a
updCtxt2-INR→ {name} {f} {a} (updCtxt2-INR .a ca) = ca



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


abstract

  updCtxt2-refl : (name : Name) (f t : Term)
                  → ¬ name ∈ names t
                  → updCtxt2 name f t
  updCtxt2-refl name f (VAR x) nn = updCtxt2-VAR _
--  updCtxt2-refl name f NAT nn = updCtxt2-NAT
  updCtxt2-refl name f QNAT nn = updCtxt2-QNAT
--  updCtxt2-refl name f TNAT nn = updCtxt2-TNAT
  updCtxt2-refl name f (LT t t₁) nn = updCtxt2-LT _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (QLT t t₁) nn = updCtxt2-QLT _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (NUM x) nn = updCtxt2-NUM _
  updCtxt2-refl name f (IFLT t t₁ t₂ t₃) nn = updCtxt2-IFLT _ _ _ _ (updCtxt2-refl name f t (¬∈++4→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₁ (¬∈++4→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₂ (¬∈++4→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₃ (¬∈++4→¬∈4 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn))
  updCtxt2-refl name f (IFEQ t t₁ t₂ t₃) nn = updCtxt2-IFEQ _ _ _ _ (updCtxt2-refl name f t (¬∈++4→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₁ (¬∈++4→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₂ (¬∈++4→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₃ (¬∈++4→¬∈4 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn))
  updCtxt2-refl name f (SUC t) nn = updCtxt2-SUC _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (NATREC t t₁ t₂) nn = updCtxt2-NATREC _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
  updCtxt2-refl name f (PI t t₁) nn = updCtxt2-PI _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (LAMBDA t) nn = updCtxt2-LAMBDA _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (MSEQ s) nn = updCtxt2-MSEQ _
  updCtxt2-refl name f (MAPP s t) nn = updCtxt2-MAPP _ _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (APPLY t t₁) nn = updCtxt2-APPLY _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (FIX t) nn = updCtxt2-FIX _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (LET t t₁) nn = updCtxt2-LET _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (SUM t t₁) nn = updCtxt2-SUM _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (PAIR t t₁) nn = updCtxt2-PAIR _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (SPREAD t t₁) nn = updCtxt2-SPREAD _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (WT t t₁ t₂) nn = updCtxt2-WT _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
  updCtxt2-refl name f (SUP t t₁) nn = updCtxt2-SUP _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (WREC t t₁) nn = updCtxt2-WREC _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (MT t t₁ t₂) nn = updCtxt2-MT _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
  updCtxt2-refl name f (SET t t₁) nn = updCtxt2-SET _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (TUNION t t₁) nn = updCtxt2-TUNION _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (ISECT t t₁) nn = updCtxt2-ISECT _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (UNION t t₁) nn = updCtxt2-UNION _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
--  updCtxt2-refl name f (QTUNION t t₁) nn = updCtxt2-QTUNION _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f (INL t) nn = updCtxt2-INL _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (INR t) nn = updCtxt2-INR _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (DECIDE t t₁ t₂) nn = updCtxt2-DECIDE _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
  updCtxt2-refl name f (EQ t t₁ t₂) nn = updCtxt2-EQ _ _ _ (updCtxt2-refl name f t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} nn)) (updCtxt2-refl name f t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} nn))
--  updCtxt2-refl name f (EQB t t₁ t₂ t₃) nn = updCtxt2-EQB _ _ _ _ (updCtxt2-refl name f t (¬∈++4→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₁ (¬∈++4→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₂ (¬∈++4→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn)) (updCtxt2-refl name f t₃ (¬∈++4→¬∈4 {_} {_} {names t} {names t₁} {names t₂} {names t₃} nn))
  updCtxt2-refl name f AX nn = updCtxt2-AX
  updCtxt2-refl name f FREE nn = updCtxt2-FREE
  updCtxt2-refl name f (CS x) nn = updCtxt2-CS _
  updCtxt2-refl name f (NAME x) nn = updCtxt2-NAME x (λ z → nn (here (sym z)))
  updCtxt2-refl name f (FRESH t) nn = updCtxt2-FRESH t (updCtxt2-refl (suc name) (shiftNameUp 0 f) t (λ z → nn (suc→∈lowerNames {name} {names t} z)))
  updCtxt2-refl name f (LOAD t) nn = updCtxt2-LOAD t --(updCtxt2-refl name f t nn)
  updCtxt2-refl name f (CHOOSE t t₁) nn = updCtxt2-CHOOSE _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
--  updCtxt2-refl name f (TSQUASH t) nn = updCtxt2-TSQUASH _ (updCtxt2-refl name f t nn)
--  updCtxt2-refl name f (TTRUNC t) nn = updCtxt2-TTRUNC _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f NOWRITE nn = updCtxt2-NOWRITE
  updCtxt2-refl name f NOREAD  nn = updCtxt2-NOREAD
  updCtxt2-refl name f (SUBSING t) nn = updCtxt2-SUBSING _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (DUM t) nn = updCtxt2-DUM _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (FFDEFS t t₁) nn = updCtxt2-FFDEFS _ _ (updCtxt2-refl name f t (¬∈++2→¬∈1 nn)) (updCtxt2-refl name f t₁ (¬∈++2→¬∈2 nn))
  updCtxt2-refl name f PURE nn = updCtxt2-PURE
  updCtxt2-refl name f NOSEQ nn = updCtxt2-NOSEQ
  updCtxt2-refl name f NOENC nn = updCtxt2-NOENC
  updCtxt2-refl name f (TERM t) nn = updCtxt2-TERM _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (ENC t) nn = updCtxt2-ENC _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (UNIV x) nn = updCtxt2-UNIV _
  updCtxt2-refl name f (LIFT t) nn = updCtxt2-LIFT _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (LOWER t) nn = updCtxt2-LOWER _ (updCtxt2-refl name f t nn)
  updCtxt2-refl name f (SHRINK t) nn = updCtxt2-SHRINK _ (updCtxt2-refl name f t nn)



updCtxt2-shiftNameUp-LAMBDA→ : (v : Var) {name : Name} {f : Term} (cf : # f) {a t : Term}
                                → t ≡ shiftNameUp v a
                                → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (LAMBDA t)
                                → (updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a) → updCtxt2 name f a)
                                → updCtxt2 name f (LAMBDA a)
updCtxt2-shiftNameUp-LAMBDA→ v {name} {f} cf {a} {t} e (updCtxt2-LAMBDA .t upd₁) ind rewrite e = updCtxt2-LAMBDA _ (ind upd₁)
updCtxt2-shiftNameUp-LAMBDA→ v {name} {f} cf {a} {.(updBody (sucIf≤ v name) (shiftNameUp v f))} e updCtxt2-upd ind
  rewrite updBody≡shiftNameUp→ v name f a e = updCtxt2-upd



abstract

  updCtxt2-shiftNameUp→ : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                           → updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a)
                           → updCtxt2 name f a
  updCtxt2-shiftNameUp→ v {name} {f} cf {VAR x} (updCtxt2-VAR .x) = updCtxt2-VAR _
--  updCtxt2-shiftNameUp→ v {name} {f} cf {NAT} upd = updCtxt2-NAT
  updCtxt2-shiftNameUp→ v {name} {f} cf {QNAT} upd = updCtxt2-QNAT
--  updCtxt2-shiftNameUp→ v {name} {f} cf {TNAT} upd = updCtxt2-TNAT
  updCtxt2-shiftNameUp→ v {name} {f} cf {LT a a₁} (updCtxt2-LT .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-LT _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {QLT a a₁} (updCtxt2-QLT .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-QLT _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {NUM x} upd = updCtxt2-NUM _
  updCtxt2-shiftNameUp→ v {name} {f} cf {IFLT a a₁ a₂ a₃} (updCtxt2-IFLT .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) .(shiftNameUp v a₃) upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃) (updCtxt2-shiftNameUp→ v cf upd₄)
  updCtxt2-shiftNameUp→ v {name} {f} cf {IFEQ a a₁ a₂ a₃} (updCtxt2-IFEQ .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) .(shiftNameUp v a₃) upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFEQ _ _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃) (updCtxt2-shiftNameUp→ v cf upd₄)
  updCtxt2-shiftNameUp→ v {name} {f} cf {SUC a} (updCtxt2-SUC .(shiftNameUp v a) upd₁) = updCtxt2-SUC _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {NATREC a a₁ a₂} (updCtxt2-NATREC .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-NATREC _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
  updCtxt2-shiftNameUp→ v {name} {f} cf {PI a a₁} (updCtxt2-PI .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-PI _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {LAMBDA a} upd =
    updCtxt2-shiftNameUp-LAMBDA→ v {name} {f} cf {a} {shiftNameUp v a} refl upd ind
    where
      ind : updCtxt2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v a) → updCtxt2 name f a
      ind = updCtxt2-shiftNameUp→ v cf
  updCtxt2-shiftNameUp→ v {name} {f} cf {APPLY a a₁} (updCtxt2-APPLY .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-APPLY _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {MSEQ s} (updCtxt2-MSEQ s) = updCtxt2-MSEQ s
  updCtxt2-shiftNameUp→ v {name} {f} cf {MAPP s a} (updCtxt2-MAPP s .(shiftNameUp v a) upd₁) = updCtxt2-MAPP _ _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {FIX a} (updCtxt2-FIX .(shiftNameUp v a) upd₁) = updCtxt2-FIX _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {LET a a₁} (updCtxt2-LET .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-LET _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {SUM a a₁} (updCtxt2-SUM .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SUM _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {PAIR a a₁} (updCtxt2-PAIR .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-PAIR _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {SPREAD a a₁} (updCtxt2-SPREAD .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SPREAD _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {WT a a₁ a₂} (updCtxt2-WT .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-WT _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
  updCtxt2-shiftNameUp→ v {name} {f} cf {SUP a a₁} (updCtxt2-SUP .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SUP _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {WREC a a₁} (updCtxt2-WREC .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-WREC _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {MT a a₁ a₂} (updCtxt2-MT .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-MT _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
  updCtxt2-shiftNameUp→ v {name} {f} cf {SET a a₁} (updCtxt2-SET .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-SET _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {TUNION a a₁} (updCtxt2-TUNION .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-TUNION _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {ISECT a a₁} (updCtxt2-ISECT .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-ISECT _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {UNION a a₁} (updCtxt2-UNION .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-UNION _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
--  updCtxt2-shiftNameUp→ v {name} {f} cf {QTUNION a a₁} (updCtxt2-QTUNION .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-QTUNION _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {INL a} (updCtxt2-INL .(shiftNameUp v a) upd₁) = updCtxt2-INL _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {INR a} (updCtxt2-INR .(shiftNameUp v a) upd₁) = updCtxt2-INR _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {DECIDE a a₁ a₂} (updCtxt2-DECIDE .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
  updCtxt2-shiftNameUp→ v {name} {f} cf {EQ a a₁ a₂} (updCtxt2-EQ .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃)
--  updCtxt2-shiftNameUp→ v {name} {f} cf {EQB a a₁ a₂ a₃} (updCtxt2-EQB .(shiftNameUp v a) .(shiftNameUp v a₁) .(shiftNameUp v a₂) .(shiftNameUp v a₃) upd₁ upd₂ upd₃ upd₄) = updCtxt2-EQB _ _ _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂) (updCtxt2-shiftNameUp→ v cf upd₃) (updCtxt2-shiftNameUp→ v cf upd₄)
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
  updCtxt2-shiftNameUp→ v {name} {f} cf {LOAD a} (updCtxt2-LOAD .a) = updCtxt2-LOAD _ --(updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {CHOOSE a a₁} (updCtxt2-CHOOSE .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-CHOOSE _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
--  updCtxt2-shiftNameUp→ v {name} {f} cf {TSQUASH a} (updCtxt2-TSQUASH .(shiftNameUp v a) upd₁) = updCtxt2-TSQUASH _ (updCtxt2-shiftNameUp→ v cf upd₁)
--  updCtxt2-shiftNameUp→ v {name} {f} cf {TTRUNC a} (updCtxt2-TTRUNC .(shiftNameUp v a) upd₁) = updCtxt2-TTRUNC _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {NOWRITE} updCtxt2-NOWRITE = updCtxt2-NOWRITE
  updCtxt2-shiftNameUp→ v {name} {f} cf {NOREAD}  updCtxt2-NOREAD  = updCtxt2-NOREAD
  updCtxt2-shiftNameUp→ v {name} {f} cf {SUBSING a} (updCtxt2-SUBSING .(shiftNameUp v a) upd₁) = updCtxt2-SUBSING _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {DUM a} (updCtxt2-DUM .(shiftNameUp v a) upd₁) = updCtxt2-DUM _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {FFDEFS a a₁} (updCtxt2-FFDEFS .(shiftNameUp v a) .(shiftNameUp v a₁) upd₁ upd₂) = updCtxt2-FFDEFS _ _ (updCtxt2-shiftNameUp→ v cf upd₁) (updCtxt2-shiftNameUp→ v cf upd₂)
  updCtxt2-shiftNameUp→ v {name} {f} cf {PURE} upd = updCtxt2-PURE
  updCtxt2-shiftNameUp→ v {name} {f} cf {NOSEQ} upd = updCtxt2-NOSEQ
  updCtxt2-shiftNameUp→ v {name} {f} cf {NOENC} upd = updCtxt2-NOENC
  updCtxt2-shiftNameUp→ v {name} {f} cf {TERM a} (updCtxt2-TERM .(shiftNameUp v a) upd₁) = updCtxt2-TERM _ (updCtxt2-shiftNameUp→ v cf upd₁)
  updCtxt2-shiftNameUp→ v {name} {f} cf {ENC a} (updCtxt2-ENC .(shiftNameUp v a) upd₁) = updCtxt2-ENC _ (updCtxt2-shiftNameUp→ v cf upd₁)
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
  ¬∈names→isHighestℕ
    cc {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {chooseT name w (NUM m)} {chooseT name w (NUM m)} {n} {name}
    (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
    (λ z → nnw (names𝕎-chooseT→ cc name name w (NUM m) z))
    (dom𝕎-chooseT cc name name w (NUM m) idom)
    g1 comp
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
  (λ z → nnw (names𝕎-chooseT→ cc name name w (NUM m) z)) ,
  dom𝕎-chooseT cc name name w (NUM m) idom
→isHighestℕ-upd-body2-NUM3b-∈names𝕎 cc gc {suc k} {name} {w} {f} {m} {m'} cf nnf nnw idom comp
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftUp 0 (ct f cf) | #shiftDown 1 (ct f cf)
        | #shiftUp 0 (ct f cf) | subv# 0 AX f cf | #shiftDown 0 (ct f cf) =
  (λ z → nnw (names𝕎-chooseT→ cc name name w (NUM m) z)) ,
  dom𝕎-chooseT cc name name w (NUM m) idom ,
  ¬∈names→∈names𝕎
    cc {k} {APPLY f (NUM m)} {APPLY f (NUM m)} {chooseT name w (NUM m)} {chooseT name w (NUM m)} {name}
    (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
    (λ z → nnw (names𝕎-chooseT→ cc name name w (NUM m) z))
    (dom𝕎-chooseT cc name name w (NUM m) idom)
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


stepsVal₁ : (a b : Term) (w w' : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (b ,  w') → b ≡ a
stepsVal₁ a b w w' n isv comp
  rewrite stepsVal a w n isv
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = refl


stepsVal₂ : (a b : Term) (w w' : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (b ,  w') → w' ≡ w
stepsVal₂ a b w w' n isv comp
  rewrite stepsVal a w n isv
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = refl


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
... |    inj₂ q with is-MSEQ a
... |       inj₁ (s , z) rewrite z = ⊥-elim (nv tt)
... |       inj₂ z rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



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



ΣhighestUpdCtxtAux2-MAPP₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {s : 𝕊} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (MAPP s a1) (MAPP s a') w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (MAPP s a) (MAPP s a') w0 w w'
ΣhighestUpdCtxtAux2-MAPP₁-aux {j} {k} {w} {w0} {w1} {w'} {s} {a} {a1} {a'} {name} {f} {n} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-MAPP₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {s : 𝕊} {a a' : Term} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (MAPP s a) (MAPP s a') w0 w w')
ΣhighestUpdCtxtAux2-MAPP₁ {0} {name} {f} {n} {s} {a} {a'} {w0} {w} {w'} (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-MAPP _ _ u
ΣhighestUpdCtxtAux2-MAPP₁ {suc k} {name} {f} {n} {s} {a} {a'} {w0} {w} {w'} (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-MAPP₁ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-MAPP₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (MAPP s a1) (MAPP s a') w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-MAPP₁ {k} {name} {f} {n} {s} {a1} {a'} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-MAPP₁ {suc k} {name} {f} {n} {s} {a} {a'} {w0} {w} {w'} (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-MAPP _ _ u



ΣhighestUpdCtxt2-MAPP₁ : {name : Name} {f : Term} {n : ℕ} {s : 𝕊} {a : Term} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (MAPP s a) w0 w
ΣhighestUpdCtxt2-MAPP₁ {name} {f} {n} {s} {a} {w0} {w} (k , a' , w' , wcomp , i , inw , u) =
  fst q , MAPP s a' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (MAPP s a) (MAPP s a') w0 w w')
    q = ΣhighestUpdCtxtAux2-MAPP₁ {k} (wcomp , i , inw , u)



stepsPresHighestℕ2-MAPP₁→ : {name : Name} {f : Term} {s : 𝕊} {a : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (MAPP s a) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-MAPP₁→ {name} {f} {s} {a} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = MAPP→hasValue k s a v w w' comp isv


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


stepsPresHighestℕ2-IFEQ₂→ : {name : Name} {f : Term} {n : ℕ} {b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (IFEQ (NUM n) b c d) w
                            → stepsPresHighestℕ2 name f b w
stepsPresHighestℕ2-IFEQ₂→ {name} {f} {n} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k b w
    hv = IFEQ-NUM→hasValue k n b c d v w w' comp isv



ΣhighestUpdCtxtAux2-IFEQ₂-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {b b1 b' : Term} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {c d : Term}
                               → ¬ isValue b
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step b w ≡ just (b1 , w1)
                               → (comp : steps k (b1 , w1) ≡ (b' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {b1} {b'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (IFEQ (NUM m) b1 c d) (IFEQ (NUM m) b' c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (IFEQ (NUM m) b c d) (IFEQ (NUM m) b' c d) w0 w w'
ΣhighestUpdCtxtAux2-IFEQ₂-aux {j} {k} {w} {w0} {w1} {w'} {b} {b1} {b'} {name} {f} {n} {m} {c} {d} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM b
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-IFEQ₂ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b b' c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxtAux2 k name f n b b' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFEQ (NUM m) b c d) (IFEQ (NUM m) b' c d) w0 w w')
ΣhighestUpdCtxtAux2-IFEQ₂ {0} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFEQ _ _ _ _ (updCtxt2-NUM m) u uc ud
ΣhighestUpdCtxtAux2-IFEQ₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , inw , u) with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ y rewrite stepVal b w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-IFEQ₂ {k} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-IFEQ₂-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFEQ (NUM m) b1 c d) (IFEQ (NUM m) b' c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-IFEQ₂ {k} {name} {f} {n} {m} {b1} {b'} {c} {d} {w0} {w1} {w'} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-IFEQ₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFEQ _ _ _ _ (updCtxt2-NUM m) u uc ud



ΣhighestUpdCtxt2-IFEQ₂ : {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b c d : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxt2 name f n b w0 w
                        → ΣhighestUpdCtxt2 name f n (IFEQ (NUM m) b c d) w0 w
ΣhighestUpdCtxt2-IFEQ₂ {name} {f} {n} {m} {b} {c} {d} {w0} {w} uc ud (k , b' , w' , wcomp , i , inw , u) =
  fst q , IFEQ (NUM m) b' c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFEQ (NUM m) b c d) (IFEQ (NUM m) b' c d) w0 w w')
    q = ΣhighestUpdCtxtAux2-IFEQ₂ {k} uc ud (wcomp , i , inw , u)



stepsPresHighestℕ2-IFEQ₁→ : {name : Name} {f : Term} {a b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (IFEQ a b c d) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-IFEQ₁→ {name} {f} {a} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = IFEQ→hasValue k a b c d v w w' comp isv



ΣhighestUpdCtxtAux2-IFEQ₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b c d : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (IFEQ a1 b c d) (IFEQ a' b c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (IFEQ a b c d) (IFEQ a' b c d) w0 w w'
ΣhighestUpdCtxtAux2-IFEQ₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} {c} {d} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-IFEQ₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFEQ a b c d) (IFEQ a' b c d) w0 w w')
ΣhighestUpdCtxtAux2-IFEQ₁ {0} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFEQ _ _ _ _ u ub uc ud
ΣhighestUpdCtxtAux2-IFEQ₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-IFEQ₁ {k} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-IFEQ₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFEQ a1 b c d) (IFEQ a' b c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-IFEQ₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {d} {w0} {w1} {w'} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-IFEQ₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-IFEQ _ _ _ _ u ub uc ud



ΣhighestUpdCtxt2-IFEQ₁ : {name : Name} {f : Term} {n : ℕ} {a b c d : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → updCtxt2 name f d
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (IFEQ a b c d) w0 w
ΣhighestUpdCtxt2-IFEQ₁ {name} {f} {n} {a} {b} {c} {d} {w0} {w} ub uc ud (k , a' , w' , wcomp , i , inw , u) =
  fst q , IFEQ a' b c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (IFEQ a b c d) (IFEQ a' b c d) w0 w w')
    q = ΣhighestUpdCtxtAux2-IFEQ₁ {k} ub uc ud (wcomp , i , inw , u)



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


ΣhighestUpdCtxtAux2-NATREC₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' b c : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (NATREC a1 b c) (NATREC a' b c) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (NATREC a b c) (NATREC a' b c) w0 w w'
ΣhighestUpdCtxtAux2-NATREC₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {b} {c} {name} {f} {n} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-NATREC₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c : Term} {w0 w w' : 𝕎·}
                            → updCtxt2 name f b
                            → updCtxt2 name f c
                            → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                            → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (NATREC a b c) (NATREC a' b c) w0 w w')
ΣhighestUpdCtxtAux2-NATREC₁ {0} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-NATREC _ _ _ u ub uc
ΣhighestUpdCtxtAux2-NATREC₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-NATREC₁ {k} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-NATREC₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (NATREC a1 b c) (NATREC a' b c) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-NATREC₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {w0} {w1} {w'} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-NATREC₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-NATREC _ _ _ u ub uc



ΣhighestUpdCtxt2-NATREC₁ : {name : Name} {f : Term} {n : ℕ} {a b c : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → updCtxt2 name f c
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (NATREC a b c) w0 w
ΣhighestUpdCtxt2-NATREC₁ {name} {f} {n} {a} {b} {c} {w0} {w} ub uc (k , a' , w' , wcomp , i , inw , u) =
  fst q , NATREC a' b c , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (NATREC a b c) (NATREC a' b c) w0 w w')
    q = ΣhighestUpdCtxtAux2-NATREC₁ {k} ub uc (wcomp , i , inw , u)



stepsPresHighestℕ2-NATREC₁→ : {name : Name} {f : Term} {a b c : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (NATREC a b c) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-NATREC₁→ {name} {f} {a} {b}{c} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = NATREC→hasValue k a b c v w w' comp isv


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


stepsPresHighestℕ2-WREC₁→ : {name : Name} {f : Term} {a b : Term} {w : 𝕎·}
                            → stepsPresHighestℕ2 name f (WREC a b) w
                            → stepsPresHighestℕ2 name f a w
stepsPresHighestℕ2-WREC₁→ {name} {f} {a} {b} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = WREC→hasValue k a b v w w' comp isv


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



ΣhighestUpdCtxtAux2-WREC₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → ¬ name ∈ names𝕎· w
                               → name ∈ dom𝕎· w
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux2 j name f n (WREC a1 b) (WREC a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux2 (suc j) name f n (WREC a b) (WREC a' b) w0 w w'
ΣhighestUpdCtxtAux2-WREC₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv nnw idom comp0 comp i (comp1 , g , inw , u) with is-SUP a
... | inj₁ (x , y , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , (nnw , idom , inw) , u



ΣhighestUpdCtxtAux2-WREC₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxtAux2 k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (WREC a b) (WREC a' b) w0 w w')
ΣhighestUpdCtxtAux2-WREC₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-WREC _ _ u ub
ΣhighestUpdCtxtAux2-WREC₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux2-WREC₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux2-WREC₁-aux {fst ind} {k} y (fst inw) (fst (snd inw)) z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (WREC a1 b) (WREC a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux2-WREC₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , snd (snd inw) , u)
ΣhighestUpdCtxtAux2-WREC₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , inw , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , inw , updCtxt2-WREC _ _ u ub



ΣhighestUpdCtxt2-WREC₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt2 name f b
                        → ΣhighestUpdCtxt2 name f n a w0 w
                        → ΣhighestUpdCtxt2 name f n (WREC a b) w0 w
ΣhighestUpdCtxt2-WREC₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , inw , u) =
  fst q , WREC a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux2 j name f n (WREC a b) (WREC a' b) w0 w w')
    q = ΣhighestUpdCtxtAux2-WREC₁ {k} ub (wcomp , i , inw , u)



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



abstract

  updCtxt2-renn : (name n m : Name) (f a : Term)
                  → ¬ name ≡ n
                  → ¬ name ≡ m
                  → ¬ n ∈ names f
                  → # f
                  → updCtxt2 name f a
                  → updCtxt2 name f (renn n m a)
  updCtxt2-renn name n m f .(VAR x) diff1 diff2 nf cf (updCtxt2-VAR x) = updCtxt2-VAR _
--  updCtxt2-renn name n m f .NAT diff1 diff2 nf cf updCtxt2-NAT = updCtxt2-NAT
  updCtxt2-renn name n m f .QNAT diff1 diff2 nf cf updCtxt2-QNAT = updCtxt2-QNAT
--  updCtxt2-renn name n m f .TNAT diff1 diff2 nf cf updCtxt2-TNAT = updCtxt2-TNAT
  updCtxt2-renn name n m f .(LT a b) diff1 diff2 nf cf (updCtxt2-LT a b upd₁ upd₂) = updCtxt2-LT _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(QLT a b) diff1 diff2 nf cf (updCtxt2-QLT a b upd₁ upd₂) = updCtxt2-QLT _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(NUM x) diff1 diff2 nf cf (updCtxt2-NUM x) = updCtxt2-NUM _
  updCtxt2-renn name n m f .(IFLT a b c d) diff1 diff2 nf cf (updCtxt2-IFLT a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFLT _ _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃) (updCtxt2-renn name n m f d diff1 diff2 nf cf upd₄)
  updCtxt2-renn name n m f .(IFEQ a b c d) diff1 diff2 nf cf (updCtxt2-IFEQ a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-IFEQ _ _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃) (updCtxt2-renn name n m f d diff1 diff2 nf cf upd₄)
  updCtxt2-renn name n m f .(SUC a) diff1 diff2 nf cf (updCtxt2-SUC a upd₁) = updCtxt2-SUC _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(NATREC a a₁ a₂) diff1 diff2 nf cf (updCtxt2-NATREC a a₁ a₂ upd₁ upd₂ upd₃) = updCtxt2-NATREC _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f a₁ diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f a₂ diff1 diff2 nf cf upd₃)
  updCtxt2-renn name n m f .(PI a b) diff1 diff2 nf cf (updCtxt2-PI a b upd₁ upd₂) = updCtxt2-PI _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(LAMBDA a) diff1 diff2 nf cf (updCtxt2-LAMBDA a upd₁) = updCtxt2-LAMBDA _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(APPLY a b) diff1 diff2 nf cf (updCtxt2-APPLY a b upd₁ upd₂) = updCtxt2-APPLY _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(MSEQ s) diff1 diff2 nf cf (updCtxt2-MSEQ s) = updCtxt2-MSEQ _
  updCtxt2-renn name n m f .(MAPP s a) diff1 diff2 nf cf (updCtxt2-MAPP s a upd₁) = updCtxt2-MAPP _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(FIX a) diff1 diff2 nf cf (updCtxt2-FIX a upd₁) = updCtxt2-FIX _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(LET a b) diff1 diff2 nf cf (updCtxt2-LET a b upd₁ upd₂) = updCtxt2-LET _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(SUM a b) diff1 diff2 nf cf (updCtxt2-SUM a b upd₁ upd₂) = updCtxt2-SUM _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(PAIR a b) diff1 diff2 nf cf (updCtxt2-PAIR a b upd₁ upd₂) = updCtxt2-PAIR _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(SPREAD a b) diff1 diff2 nf cf (updCtxt2-SPREAD a b upd₁ upd₂) = updCtxt2-SPREAD _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(WT a b c) diff1 diff2 nf cf (updCtxt2-WT a b c upd₁ upd₂ upd₃) = updCtxt2-WT _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃)
  updCtxt2-renn name n m f .(SUP a b) diff1 diff2 nf cf (updCtxt2-SUP a b upd₁ upd₂) = updCtxt2-SUP _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(WREC a b) diff1 diff2 nf cf (updCtxt2-WREC a b upd₁ upd₂) = updCtxt2-WREC _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(MT a b c) diff1 diff2 nf cf (updCtxt2-MT a b c upd₁ upd₂ upd₃) = updCtxt2-MT _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃)
  updCtxt2-renn name n m f .(SET a b) diff1 diff2 nf cf (updCtxt2-SET a b upd₁ upd₂) = updCtxt2-SET _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(ISECT a b) diff1 diff2 nf cf (updCtxt2-ISECT a b upd₁ upd₂) = updCtxt2-ISECT _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(TUNION a b) diff1 diff2 nf cf (updCtxt2-TUNION a b upd₁ upd₂) = updCtxt2-TUNION _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(UNION a b) diff1 diff2 nf cf (updCtxt2-UNION a b upd₁ upd₂) = updCtxt2-UNION _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
--  updCtxt2-renn name n m f .(QTUNION a b) diff1 diff2 nf cf (updCtxt2-QTUNION a b upd₁ upd₂) = updCtxt2-QTUNION _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(INL a) diff1 diff2 nf cf (updCtxt2-INL a upd₁) = updCtxt2-INL _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(INR a) diff1 diff2 nf cf (updCtxt2-INR a upd₁) = updCtxt2-INR _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(DECIDE a b c) diff1 diff2 nf cf (updCtxt2-DECIDE a b c upd₁ upd₂ upd₃) = updCtxt2-DECIDE _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃)
  updCtxt2-renn name n m f .(EQ a b c) diff1 diff2 nf cf (updCtxt2-EQ a b c upd₁ upd₂ upd₃) = updCtxt2-EQ _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃)
--  updCtxt2-renn name n m f .(EQB a b c d) diff1 diff2 nf cf (updCtxt2-EQB a b c d upd₁ upd₂ upd₃ upd₄) = updCtxt2-EQB _ _ _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂) (updCtxt2-renn name n m f c diff1 diff2 nf cf upd₃) (updCtxt2-renn name n m f d diff1 diff2 nf cf upd₄)
  updCtxt2-renn name n m f .AX diff1 diff2 nf cf updCtxt2-AX = updCtxt2-AX
  updCtxt2-renn name n m f .FREE diff1 diff2 nf cf updCtxt2-FREE = updCtxt2-FREE
  updCtxt2-renn name n m f .(CS name') diff1 diff2 nf cf (updCtxt2-CS name') with name' ≟ n
  ... | yes _ = updCtxt2-CS _
  ... | no _ = updCtxt2-CS _
  updCtxt2-renn name n m f .(NAME name') diff1 diff2 nf cf (updCtxt2-NAME name' x) with name' ≟ n
  ... | yes _ = updCtxt2-NAME _ (λ z → diff2 (sym z))
  ... | no _ = updCtxt2-NAME _ x
  updCtxt2-renn name n m f .(FRESH a) diff1 diff2 nf cf (updCtxt2-FRESH a upd₁) = updCtxt2-FRESH _ (updCtxt2-renn (suc name) (suc n) (suc m) (shiftNameUp 0 f) a (λ z → diff1 (suc-injective z)) (λ z → diff2 (suc-injective z)) (→¬s∈names-shiftNameUp n f nf) (→#shiftNameUp 0 {f} cf) upd₁)
  updCtxt2-renn name n m f .(LOAD a) diff1 diff2 nf cf (updCtxt2-LOAD a) = updCtxt2-LOAD _ --(updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(CHOOSE a b) diff1 diff2 nf cf (updCtxt2-CHOOSE a b upd₁ upd₂) = updCtxt2-CHOOSE _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
--  updCtxt2-renn name n m f .(TSQUASH a) diff1 diff2 nf cf (updCtxt2-TSQUASH a upd₁) = updCtxt2-TSQUASH _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
--  updCtxt2-renn name n m f .(TTRUNC a) diff1 diff2 nf cf (updCtxt2-TTRUNC a upd₁) = updCtxt2-TTRUNC _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .NOWRITE diff1 diff2 nf cf updCtxt2-NOWRITE = updCtxt2-NOWRITE
  updCtxt2-renn name n m f .NOREAD  diff1 diff2 nf cf updCtxt2-NOREAD  = updCtxt2-NOREAD
  updCtxt2-renn name n m f .(SUBSING a) diff1 diff2 nf cf (updCtxt2-SUBSING a upd₁) = updCtxt2-SUBSING _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .PURE diff1 diff2 nf cf updCtxt2-PURE = updCtxt2-PURE
  updCtxt2-renn name n m f .NOSEQ diff1 diff2 nf cf updCtxt2-NOSEQ = updCtxt2-NOSEQ
  updCtxt2-renn name n m f .NOENC diff1 diff2 nf cf updCtxt2-NOENC = updCtxt2-NOENC
  updCtxt2-renn name n m f .(TERM a) diff1 diff2 nf cf (updCtxt2-TERM a upd₁) = updCtxt2-TERM _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(ENC a) diff1 diff2 nf cf (updCtxt2-ENC a upd₁) = updCtxt2-ENC _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(DUM a) diff1 diff2 nf cf (updCtxt2-DUM a upd₁) = updCtxt2-DUM _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(FFDEFS a b) diff1 diff2 nf cf (updCtxt2-FFDEFS a b upd₁ upd₂) = updCtxt2-FFDEFS _ _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁) (updCtxt2-renn name n m f b diff1 diff2 nf cf upd₂)
  updCtxt2-renn name n m f .(UNIV x) diff1 diff2 nf cf (updCtxt2-UNIV x) = updCtxt2-UNIV _
  updCtxt2-renn name n m f .(LIFT a) diff1 diff2 nf cf (updCtxt2-LIFT a upd₁) = updCtxt2-LIFT _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(LOWER a) diff1 diff2 nf cf (updCtxt2-LOWER a upd₁) = updCtxt2-LOWER _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(SHRINK a) diff1 diff2 nf cf (updCtxt2-SHRINK a upd₁) = updCtxt2-SHRINK _ (updCtxt2-renn name n m f a diff1 diff2 nf cf upd₁)
  updCtxt2-renn name n m f .(upd name f) diff1 diff2 nf cf updCtxt2-upd with name ≟ n
  ... | yes p rewrite p = ⊥-elim (diff1 refl)
  ... | no p rewrite renn¬∈ n m (shiftUp 0 f) (→¬∈names-shiftUp {n} {0} {f} nf) = updCtxt2-upd


getT≤ℕ-startNewChoices→ : (cc : ContConds) (w : 𝕎·) (a : Term) (n : ℕ) (name : Name)
                            → name ∈ dom𝕎· w
                            → getT≤ℕ (startNewChoices Res⊤ w a) n name
                            → getT≤ℕ w n name
getT≤ℕ-startNewChoices→ cc w a n name idom (j , g , x) =
  j , trans (sym (getT-startNewChoices≡ cc name w a 0 idom)) g , x


ΣhighestUpdCtxt2-startNewChoices : (cc : ContConds) (name : Name) (f : Term) (n : ℕ) (w : 𝕎·) (a : Term)
                                   → ¬ name ∈ names𝕎· w
                                   → name ∈ dom𝕎· w
                                   → ΣhighestUpdCtxt2 name f n AX w (startNewChoices Res⊤ w a)
ΣhighestUpdCtxt2-startNewChoices cc name f n w a niw idom =
  0 , AX , startNewChoices Res⊤ w a , refl , g , (nn , nd) , updCtxt2-AX
  where
    g : getT≤ℕ (startNewChoices Res⊤ w a) n name
        → getT≤ℕ w n name × getT≤ℕ (startNewChoices Res⊤ w a) n name
    g h = getT≤ℕ-startNewChoices→ cc w a n name idom h , h

    nn : ¬ name ∈ names𝕎· (startNewChoices Res⊤ w a)
    nn = →¬names𝕎-startNewChoices cc w a name niw

    nd : name ∈ dom𝕎· (startNewChoices Res⊤ w a)
    nd = ⊆dom𝕎-startNewChoices cc w a idom


updCtxt2-WRECr : {name : Name} {f : Term} {r g : Term} (cf : # f)
               → updCtxt2 name f r
               → updCtxt2 name f g
               → updCtxt2 name f (WRECr r g)
updCtxt2-WRECr {name} {f} {r} {g} cf dr df =
  updCtxt2-LAMBDA
    _
    (updCtxt2-WREC
      _ _
      (updCtxt2-APPLY _ _ (→updCtxt2-shiftUp 0 cf df) (updCtxt2-VAR 0))
      (→updCtxt2-shiftUp 3 cf dr))


updCtxt2-BOT : (name : Name) (f : Term)
               → updCtxt2 name f BOT
updCtxt2-BOT name f = updCtxt2-FIX ID (updCtxt2-LAMBDA (VAR 0) (updCtxt2-VAR _))


updCtxt2-ENCr : {name : Name} {f : Term} {a : Term}
               → updCtxt2 name f a
               → updCtxt2 name f (ENCr a)
updCtxt2-ENCr {name} {f} {a} u =
  updCtxt2-IFEQ
    (APPLY a (NUM (encode· (ENC a)))) N0 BOT N0
    (updCtxt2-APPLY a (NUM (encode· (ENC a))) u (updCtxt2-NUM _))
    (updCtxt2-NUM _)
    (updCtxt2-BOT name f)
    (updCtxt2-NUM _)


updCtxt2-NATRECr : {name : Name} {f : Term} {n : ℕ} {b c : Term} (cf : # f)
                 → updCtxt2 name f b
                 → updCtxt2 name f c
                 → updCtxt2 name f (NATRECr n b c)
updCtxt2-NATRECr {name} {f} {0} {b} {c} cf ub uc = ub
updCtxt2-NATRECr {name} {f} {suc n} {b} {c} cf ub uc =
  updCtxt2-APPLY _ _ (updCtxt2-APPLY _ _ uc (updCtxt2-NUM _)) (updCtxt2-NATREC _ _ _ (updCtxt2-NUM _) ub uc)

\end{code}
